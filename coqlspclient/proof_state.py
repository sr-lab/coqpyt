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
    ProofStep,
    FileContext,
    Step,
    Term,
    ProofTerm,
    TermType,
)
from coqlspclient.coq_lsp_structs import (
    CoqError,
    CoqErrorCodes,
    Result,
    Query,
    GoalAnswer,
)
from coqlspclient.coq_file import CoqFile
from coqlspclient.coq_lsp_client import CoqLspClient
from typing import List, Optional, Tuple


class _AuxFile(object):
    def __init__(self, file_path: Optional[str] = None, timeout: int = 2):
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
        if not (isinstance(e, ResponseError) and e.code == ErrorCodes.ServerQuit.value):
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
                diagnostic.range["start"]["line"] : diagnostic.range["end"]["line"] + 1
            ]
            if len(command) == 1:
                command[0] = command[0][
                    diagnostic.range["start"]["character"] : diagnostic.range["end"][
                        "character"
                    ]
                    + 1
                ]
            else:
                command[0] = command[0][diagnostic.range["start"]["character"] :]
                command[-1] = command[-1][: diagnostic.range["end"]["character"] + 1]
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
                    if result.range["start"]["line"] == line:
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
                ).split("\n")[-1][:-1]
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
        def traverse_ast(el):
            if isinstance(el, dict):
                return [x for v in el.values() for x in traverse_ast(v)]
            elif isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                id = ".".join([l[1] for l in el[1][1][::-1]] + [el[2][1]])
                term = self.__get_term(id)
                return [] if term is None else [(lambda x: x, term)]
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

                return [
                    (__search_notation, (el[2][1], self.__locate, el[2][1], line))
                ] + traverse_ast(el[1:])
            elif isinstance(el, list):
                return [x for v in el for x in traverse_ast(v)]

            return []

        return traverse_ast(self.__current_step.ast.span)

    def __step(self):
        self.__current_step = self.coq_file.exec()[0]
        self.__aux_file.append(self.__current_step.text)

    def __get_steps(self) -> List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]:
        steps = []
        while self.coq_file.in_proof and not self.coq_file.checked:
            try:
                goals = self.coq_file.current_goals()
            except Exception as e:
                self.__aux_file.close()
                raise e

            self.__step()
            context_calls = self.__step_context()
            steps.append((self.__current_step, goals, context_calls))

        if self.coq_file.checked and self.coq_file.in_proof:
            return None

        return steps

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

    def __get_proofs(self) -> List[ProofTerm]:
        def call_context(calls: List[Tuple]):
            context, calls = [], [call[0](*call[1:]) for call in calls]
            [context.append(call) for call in calls if call not in context]
            context = list(filter(lambda term: term is not None, context))
            return context

        def get_proof_step(step: Tuple[Step, Optional[GoalAnswer], List[Tuple]]):
            return ProofStep(step[0], step[1], call_context(step[2]))

        proofs: List[
            Tuple[Term, List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]]
        ] = []
        statement_context = None
        while not self.coq_file.checked:
            self.__step()
            # Get context from initial statement
            if CoqFile.get_term_type(self.__current_step.ast) != TermType.OTHER:
                statement_context = self.__step_context()
            if self.coq_file.in_proof:
                steps = self.__get_steps()
                if steps is not None:
                    proofs.append((self.__get_last_term(), statement_context, steps))

        try:
            self.__aux_file.didOpen()
        except Exception as e:
            self.coq_file.close()
            raise e

        proof_steps = [
            (term, call_context(context), list(map(get_proof_step, steps)))
            for term, context, steps in proofs
        ]
        return list(map(lambda t: ProofTerm(t[0], t[1], t[2]), proof_steps))

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
