import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import (
    TextDocumentItem,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    ResponseError,
    ErrorCodes,
)
from coqlspclient.coq_structs import (
    TermType,
    CoqErrorCodes,
    CoqError,
    Step,
    Term,
    ProofStep,
    ProofTerm,
    FileContext,
)
from coqlspclient.coq_lsp_structs import Result, Query, GoalAnswer
from coqlspclient.coq_file import CoqFile
from coqlspclient.coq_lsp_client import CoqLspClient
from typing import List, Dict, Optional, Tuple


class _AuxFile(object):
    def __init__(self, file_path: Optional[str] = None, timeout: int = 30):
        self.__init_path(file_path)
        uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path):
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        with open(new_path, "w"):
            # Create empty file
            pass

        if file_path is not None:
            shutil.copyfile(file_path, new_path)

        self.path = new_path
        self.version = 1

    def read(self):
        with open(self.path, "r") as f:
            return f.read()

    def write(self, text):
        with open(self.path, "w") as f:
            f.write(text)

    def append(self, text):
        with open(self.path, "a") as f:
            f.write(text)

    def __handle_exception(self, e):
        if not isinstance(e, ResponseError) or e.code not in [
            ErrorCodes.ServerQuit.value,
            ErrorCodes.ServerTimeout.value,
        ]:
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        os.remove(self.path)

    def didOpen(self):
        uri = f"file://{self.path}"
        try:
            self.coq_lsp_client.didOpen(TextDocumentItem(uri, "coq", 1, self.read()))
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def didChange(self):
        uri = f"file://{self.path}"
        self.version += 1
        try:
            self.coq_lsp_client.didChange(
                VersionedTextDocumentIdentifier(uri, self.version),
                [TextDocumentContentChangeEvent(None, None, self.read())],
            )
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def __get_queries(self, keyword):
        uri = f"file://{self.path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return []

        searches = {}
        lines = self.read().split("\n")
        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            command = lines[
                diagnostic.range.start.line : diagnostic.range.end.line + 1
            ]
            if len(command) == 1:
                command[0] = command[0][
                    diagnostic.range.start.character : diagnostic.range.end.character + 1
                ]
            else:
                command[0] = command[0][diagnostic.range.start.character :]
                command[-1] = command[-1][: diagnostic.range.end.character + 1]
            command = "".join(command).strip()

            if command.startswith(keyword):
                query = command[len(keyword) + 1 : -1]
                if query not in searches:
                    searches[query] = []
                searches[query].append(Result(diagnostic.range, diagnostic.message))

        res = []
        for query, results in searches.items():
            res.append(Query(query, results))

        return res

    def get_diagnostics(self, keyword, search, line):
        for query in self.__get_queries(keyword):
            if query.query == f"{search}":
                for result in query.results:
                    if result.range.start.line == line:
                        return result.message
                break
        return None

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.path)

    @staticmethod
    def get_context(file_path: str, timeout: int):
        with _AuxFile(file_path=file_path, timeout=timeout) as aux_file:
            aux_file.append("\nPrint Libraries.")
            aux_file.didOpen()

            last_line = len(aux_file.read().split("\n")) - 1
            libraries = aux_file.get_diagnostics("Print Libraries", "", last_line)
            libraries = list(
                map(lambda line: line.strip(), libraries.split("\n")[1:-1])
            )
            for library in libraries:
                aux_file.append(f"\nLocate Library {library}.")
            aux_file.didChange()

            context = FileContext()
            for i, library in enumerate(libraries):
                v_file = aux_file.get_diagnostics(
                    "Locate Library", library, last_line + i + 1
                ).split()[-1][:-1]
                coq_file = CoqFile(v_file, library=library, timeout=timeout)
                coq_file.run()

                # FIXME: we ignore the usage of Local from imported files to
                # simplify the implementation. However, they can be used:
                # https://coq.inria.fr/refman/language/core/modules.html?highlight=local#coq:attr.local
                for term in list(coq_file.context.terms.keys()):
                    if coq_file.context.terms[term].text.startswith("Local"):
                        coq_file.context.terms.pop(term)

                context.update(**vars(coq_file.context))
                coq_file.close()

        return context


class ProofState(object):
    """Allows to get information about the proofs of a Coq file.
    ProofState will run the file from its current state, i.e., if the file
    has finished its execution, ProofState won't return anything. The Coq file
    will be fully checked after the creation of a ProofState.

    Attributes:
        coq_file (CoqFile): Coq file to interact with
    """

    def __init__(self, coq_file: CoqFile):
        """Creates a ProofState

        Args:
            coq_file (CoqFile): Coq file to interact with

        Raises:
            CoqError: If the provided file is not valid.
        """
        self.coq_file = coq_file
        if not self.coq_file.is_valid:
            self.coq_file.close()
            raise CoqError(
                CoqErrorCodes.InvalidFile,
                f"At least one error found in file {coq_file.path}",
            )
        self.coq_file.context = _AuxFile.get_context(coq_file.path, coq_file.timeout)
        self.__aux_file = _AuxFile(timeout=coq_file.timeout)
        self.__current_step = None
        self.__program_context: Dict[str, Tuple[Term, List]] = {}
        self.__proofs = self.__get_proofs()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __get_term(self, name):
        for i in range(len(self.coq_file.curr_module), -1, -1):
            curr_name = ".".join(self.coq_file.curr_module[:i] + [name])
            if curr_name in self.coq_file.context.terms:
                return self.coq_file.context.terms[curr_name]
        return None

    def __locate(self, search, line):
        nots = self.__aux_file.get_diagnostics("Locate", f'"{search}"', line).split(
            "\n"
        )
        fun = lambda x: x.endswith("(default interpretation)")
        return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __step_context(self):
        def traverse_expr(expr):
            stack, res = expr[:0:-1], []
            while len(stack) > 0:
                el = stack.pop()
                if isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                    term = self.__get_term(CoqFile.get_id(el))
                    if term is not None:
                        res.append((lambda x: x, term))
                elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                    line = len(self.__aux_file.read().split("\n"))
                    self.__aux_file.append(f'\nLocate "{el[2][1]}".')

                    def __search_notation(call):
                        notation_name = call[0]
                        scope = ""
                        notation = call[1](*call[2:])
                        if notation == "Unknown notation":
                            return None
                        if notation.split(":")[-1].endswith("_scope"):
                            scope = notation.split(":")[-1].strip()
                        return self.context.get_notation(notation_name, scope)

                    res.append(
                        (__search_notation, (el[2][1], self.__locate, el[2][1], line))
                    )
                    stack.append(el[1:])
                elif isinstance(el, list):
                    for v in reversed(el):
                        if isinstance(v, (dict, list)):
                            stack.append(v)
                elif isinstance(el, dict):
                    for v in reversed(el.values()):
                        if isinstance(v, (dict, list)):
                            stack.append(v)
            return res

        return traverse_expr(CoqFile.expr(self.__current_step.ast))

    def __get_last_term(self):
        terms = self.coq_file.terms
        if len(terms) == 0:
            return None
        last_term = terms[0]
        for term in terms[1:]:
            if (term.ast.range.end.line > last_term.ast.range.end.line) or (
                term.ast.range.end.line == last_term.ast.range.end.line
                and term.ast.range.end.character > last_term.ast.range.end.character
            ):
                last_term = term
        return last_term

    def __get_program_context(self):
        def traverse_expr(expr):
            stack = expr[:0:-1]
            while len(stack) > 0:
                el = stack.pop()
                if isinstance(el, list):
                    ident = CoqFile.get_ident(el)
                    if ident is not None:
                        return ident

                    for v in reversed(el):
                        if isinstance(v, list):
                            stack.append(v)
            return None

        # Tags:
        # 0 - Obligation N of id : type
        # 1 - Obligation N of id
        # 2 - Obligation N : type
        # 3 - Obligation N
        # 4 - Next Obligation of id
        # 5 - Next Obligation
        tag = CoqFile.expr(self.__current_step.ast)[1][1]
        if tag in [0, 1, 4]:
            id = traverse_expr(CoqFile.expr(self.__current_step.ast))
            # This works because the obligation must be in the
            # same module as the program
            id = ".".join(self.coq_file.curr_module + [id])
            return self.__program_context[id]
        elif tag in [2, 3, 5]:
            id = self.coq_file.current_goals().program[0][0][1]
            # This works because the obligation must be in the
            # same module as the program
            id = ".".join(self.coq_file.curr_module + [id])
            return self.__program_context[id]
        text = self.__get_last_term().text
        raise RuntimeError(f"Unknown obligation command with tag number {tag}: {text}")

    def __check_program(self):
        goals = self.coq_file.current_goals()
        if len(goals.program) == 0:
            return
        id = ".".join(self.coq_file.curr_module + [goals.program[-1][0][1]])
        if id in self.__program_context:
            return
        self.__program_context[id] = (self.__get_last_term(), self.__step_context())

    def __step(self):
        self.__current_step = self.coq_file.exec()[0]
        self.__aux_file.append(self.__current_step.text)
        self.__check_program()

    def __get_steps(
        self, proofs
    ) -> List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]:
        steps = []
        while self.coq_file.in_proof and not self.coq_file.checked:
            try:
                goals = self.coq_file.current_goals()
            except Exception as e:
                self.__aux_file.close()
                raise e

            self.__step()
            if CoqFile.get_term_type(self.__current_step.ast) != TermType.OTHER:
                self.__get_proof(proofs)
                # Pass Qed if it exists
                while not self.coq_file.in_proof and not self.coq_file.checked:
                    self.__step()
                continue
            if CoqFile.expr(self.__current_step.ast)[0] == "VernacProof":
                continue
            context_calls = self.__step_context()
            steps.append((self.__current_step, goals, context_calls))

        if self.coq_file.checked and self.coq_file.in_proof:
            return None

        return steps

    def __get_proof(self, proofs):
        term, statement_context = None, None
        if CoqFile.get_term_type(self.__current_step.ast) == TermType.OBLIGATION:
            term, statement_context = self.__get_program_context()
        elif CoqFile.get_term_type(self.__current_step.ast) != TermType.OTHER:
            term = self.__get_last_term()
            statement_context = self.__step_context()
        # HACK: We ignore proofs inside a Module Type since they can't be used outside
        # and should be overriden.
        if self.coq_file.in_proof and len(self.coq_file.curr_module_type) == 0:
            steps = self.__get_steps(proofs)
            if steps is not None:
                proofs.append((term, statement_context, steps))

    def __get_proofs(self) -> List[ProofTerm]:
        def call_context(calls: List[Tuple]):
            context, calls = [], [call[0](*call[1:]) for call in calls]
            [context.append(call) for call in calls if call not in context]
            return list(filter(lambda term: term is not None, context))

        def get_proof_step(step: Tuple[Step, Optional[GoalAnswer], List[Tuple]]):
            return ProofStep(step[0], step[1], call_context(step[2]))

        proofs: List[
            Tuple[Term, List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]]
        ] = []
        while not self.coq_file.checked:
            self.__step()
            # Get context from initial statement
            self.__get_proof(proofs)

        try:
            self.__aux_file.didOpen()
        except Exception as e:
            self.coq_file.close()
            raise e

        proof_steps = [
            (term, call_context(calls), list(map(get_proof_step, steps)))
            for term, calls, steps in proofs
        ]
        return list(map(lambda t: ProofTerm(*t), proof_steps))

    @property
    def proofs(self) -> List[ProofTerm]:
        """Gets all the proofs in the file and their corresponding steps.

        Returns:
            List[ProofStep]: Each element has the list of steps for a single
                proof of the Coq file. The proofs are ordered by the order
                they are written on the file. The steps include the context
                used for each step and the goals in that step.
        """
        return self.__proofs

    @property
    def context(self) -> FileContext:
        """
        Returns:
            FileContext: Whole context available in the environment of the Coq file.
        """
        return self.coq_file.context

    def close(self):
        """Closes all resources used by this object."""
        self.coq_file.close()
        self.__aux_file.close()
