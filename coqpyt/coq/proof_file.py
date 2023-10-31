import os
import hashlib
import shutil
import uuid
import tempfile
from coqpyt.lsp.structs import (
    TextDocumentItem,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    ResponseError,
    ErrorCodes,
)
from coqpyt.coq.structs import (
    TermType,
    Step,
    Term,
    ProofStep,
    ProofTerm,
    FileContext,
)
from coqpyt.coq.lsp.structs import Result, Query, GoalAnswer, Range
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.lsp.client import CoqLspClient
from coqpyt.coq.changes import *
from coqpyt.coq.exceptions import *
from typing import List, Dict, Optional, Tuple


class _AuxFile(object):
    __CACHE: Dict[Tuple[str, str], FileContext] = {}

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
            command = lines[diagnostic.range.start.line : diagnostic.range.end.line + 1]
            if len(command) == 0:
                continue
            elif len(command) == 1:
                command[0] = command[0][
                    diagnostic.range.start.character : diagnostic.range.end.character
                    + 1
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

                with open(v_file, "r") as f:
                    hash = hashlib.md5(f.read().encode("utf-8")).hexdigest()
                if (v_file, hash) in _AuxFile.__CACHE:
                    aux_context = _AuxFile.__CACHE[(v_file, hash)]
                else:
                    coq_file = CoqFile(v_file, library=library, timeout=timeout)
                    coq_file.run()
                    aux_context = coq_file.context
                    _AuxFile.__CACHE[(v_file, hash)] = aux_context
                    coq_file.close()

                # FIXME: we ignore the usage of Local from imported files to
                # simplify the implementation. However, they can be used:
                # https://coq.inria.fr/refman/language/core/modules.html?highlight=local#coq:attr.local
                for term in list(aux_context.terms.keys()):
                    if aux_context.terms[term].text.startswith("Local"):
                        aux_context.terms.pop(term)
                context.update(**vars(aux_context))

        return context


class ProofFile(CoqFile):
    """Allows to get information about the proofs of a Coq file.
    ProofState will run the file from its current state, i.e., if the file
    has finished its execution, ProofState won't return anything. The Coq file
    will be fully checked after the creation of a ProofState.
    """

    def __init__(
        self,
        file_path: str,
        library: Optional[str] = None,
        timeout: int = 30,
        workspace: Optional[str] = None,
        coq_lsp: str = "coq-lsp",
        coqtop: str = "coqtop",
    ):
        """Creates a ProofFile.

        Args:
            file_path (str): Absolute path of the Coq file.
            library (Optional[str], optional): The library of the file. Defaults to None.
            timeout (int, optional): Timeout used in coq-lsp. Defaults to 2.
            workspace(Optional[str], optional): Absolute path for the workspace.
                If the workspace is not defined, the workspace is equal to the
                path of the file.
            coq_lsp(str, optional): Path to the coq-lsp binary. Defaults to "coq-lsp".
            coqtop(str, optional): Path to the coqtop binary used to compile the Coq libraries
                imported by coq-lsp. This is NOT passed as a parameter to coq-lsp, it is
                simply used to check the Coq version in use. Defaults to "coqtop".
        """
        super().__init__(file_path, library, timeout, workspace, coq_lsp, coqtop)
        self.__aux_file = _AuxFile(timeout=self.timeout)

        try:
            # We need to update the context already defined in the CoqFile
            self.context.update(_AuxFile.get_context(self.path, self.timeout).terms)
            self.__program_context: Dict[str, Tuple[Term, List]] = {}
            self.__proofs = self.__get_proofs()
        except Exception as e:
            self.close()
            raise e

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __get_term(self, name):
        for i in range(len(self.curr_module), -1, -1):
            curr_name = ".".join(self.curr_module[:i] + [name])
            if curr_name in self.context.terms:
                return self.context.terms[curr_name]
        return None

    def __locate(self, search, line):
        nots = self.__aux_file.get_diagnostics("Locate", f'"{search}"', line).split(
            "\n"
        )
        fun = lambda x: x.endswith("(default interpretation)")
        return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __step_context(self, step: Step):
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

        return traverse_expr(self.expr(step.ast))

    def __get_last_term(self):
        terms = self.terms
        if len(terms) == 0:
            return None
        last_term = terms[0]
        for term in terms[1:]:
            if last_term.ast.range.end < term.ast.range.end:
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
        tag = self.expr(self.prev_step.ast)[1][1]
        if tag in [0, 1, 4]:
            id = traverse_expr(self.expr(self.prev_step.ast))
            # This works because the obligation must be in the
            # same module as the program
            id = ".".join(self.curr_module + [id])
            return self.__program_context[id]
        elif tag in [2, 3, 5]:
            id = self.current_goals().program[0][0][1]
            # This works because the obligation must be in the
            # same module as the program
            id = ".".join(self.curr_module + [id])
            return self.__program_context[id]
        text = self.__get_last_term().text
        raise RuntimeError(f"Unknown obligation command with tag number {tag}: {text}")

    def __check_program(self):
        goals = self.current_goals()
        if len(goals.program) == 0:
            return
        id = ".".join(self.curr_module + [goals.program[-1][0][1]])
        if id in self.__program_context:
            return
        self.__program_context[id] = (
            self.__get_last_term(),
            self.__step_context(self.prev_step),
        )

    def __step(self):
        self.exec()
        self.__aux_file.append(self.prev_step.text)
        self.__check_program()

    def __get_steps(
        self, proofs
    ) -> List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]:
        steps = []
        while self.in_proof and not self.checked:
            try:
                goals = self.current_goals()
            except Exception as e:
                self.__aux_file.close()
                raise e

            self.__step()
            # Nested proofs
            if self.get_term_type(self.prev_step.ast) != TermType.OTHER:
                self.__get_proof(proofs)
                # Pass Qed if it exists
                while not self.in_proof and not self.checked:
                    self.__step()
                continue
            context_calls = self.__step_context(self.prev_step)
            if self.prev_step.text.strip() == "":
                continue
            steps.append((self.prev_step, goals, context_calls))

        try:
            goals = self.current_goals()
        except Exception as e:
            self.__aux_file.close()
            raise e
        if (
            self.steps_taken < len(self.steps)
            and self.expr(self.curr_step.ast)[0] == "VernacEndProof"
        ):
            steps.append((self.curr_step, goals, []))

        return steps

    def __get_proof(self, proofs):
        term, statement_context = None, None
        if self.get_term_type(self.prev_step.ast) == TermType.OBLIGATION:
            term, statement_context = self.__get_program_context()
        elif self.get_term_type(self.prev_step.ast) != TermType.OTHER:
            term = self.__get_last_term()
            statement_context = self.__step_context(self.prev_step)
        # HACK: We ignore proofs inside a Module Type since they can't be used outside
        # and should be overriden.
        if self.in_proof and len(self.curr_module_type) == 0:
            steps = self.__get_steps(proofs)
            proofs.append((term, statement_context, steps))

    def __call_context(self, calls: List[Tuple]):
        context, calls = [], [call[0](*call[1:]) for call in calls]
        [context.append(call) for call in calls if call not in context]
        return list(filter(lambda term: term is not None, context))

    def __get_proofs(self) -> List[ProofTerm]:
        def get_proof_step(step: Tuple[Step, Optional[GoalAnswer], List[Tuple]]):
            return ProofStep(step[0], step[1], self.__call_context(step[2]))

        proofs: List[
            Tuple[Term, List[Tuple[Step, Optional[GoalAnswer], List[Tuple]]]]
        ] = []
        while not self.checked:
            self.__step()
            # Get context from initial statement
            self.__get_proof(proofs)

        try:
            self.__aux_file.didOpen()
        except Exception as e:
            self.close()
            raise e

        proof_steps = [
            (term, self.__call_context(calls), list(map(get_proof_step, steps)))
            for term, calls, steps in proofs
        ]
        return list(map(lambda t: ProofTerm(*t), proof_steps))

    def __find_step(self, range: Range) -> Optional[Tuple[ProofTerm, int]]:
        for proof in self.proofs:
            for i, proof_step in enumerate(proof.steps):
                if proof_step.ast.range == range:
                    return (proof, i)
        return None

    def __find_prev(self, range: Range) -> Tuple[ProofTerm, Optional[int]]:
        optional = self.__find_step(range)
        if optional is not None:
            return optional

        # Previous step may be the definition of the proof
        for proof in self.proofs:
            if proof.ast.range == range:
                return (proof, -1)

        raise NotImplementedError(
            "Adding steps outside of a proof is not implemented yet"
        )

    def __get_step(self, step_index):
        self.__aux_file.write("")
        for step in self.steps[: step_index + 1]:
            self.__aux_file.append(step.text)
        call = self.__step_context(self.steps[step_index])
        self.__aux_file.didChange()

        context = self.__call_context(call)
        # The goals will be loaded if used (Lazy Loading)
        goals = self._goals
        return ProofStep(self.steps[step_index], goals, context)

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

    def add_step(self, step_text: str, previous_step_index: int):
        proof, prev = self.__find_prev(self.steps[previous_step_index].ast.range)
        if prev == -1:
            self._make_change(self._add_step, step_text, previous_step_index)
        else:
            self._make_change(self._add_step, step_text, previous_step_index, True)
        proof.steps.insert(prev + 1, self.__get_step(previous_step_index + 1))
        # We should change the goals of all the steps in the same proof
        # after the one that was changed
        # NOTE: We assume the proofs and steps are in the order they are written
        for e in range(prev + 2, len(proof.steps)):
            # The goals will be loaded if used (Lazy Loading)
            proof.steps[e].goals = self._goals

    def delete_step(self, step_index: int) -> None:
        step = self.steps[step_index]
        optional = self.__find_step(step.ast.range)
        if optional is None:
            raise NotImplementedError(
                "Deleting steps outside of a proof is not implemented yet"
            )

        proof, i = optional
        proof.steps.pop(i)
        for e in range(i, len(proof.steps)):
            # The goals will be loaded if used (Lazy Loading)
            proof.steps[e].goals = self._goals
        self._make_change(self._delete_step, step_index, True)

    def change_steps(self, changes: List[CoqChange]):
        offset_steps = 0
        previous_steps_size = len(self.steps)

        for change in changes:
            if isinstance(change, CoqAddStep):
                proof, i = self.__find_prev(
                    self.steps[change.previous_step_index].ast.range
                )
                self._add_step(
                    change.step_text,
                    change.previous_step_index,
                    in_proof=True,
                    validate_file=False,
                )
                proof.steps.insert(
                    i + 1, self.__get_step(change.previous_step_index + 1)
                )
                i += 2
                offset_steps += 1
            elif isinstance(change, CoqDeleteStep):
                optional = self.__find_step(self.steps[change.step_index].ast.range)
                if optional is None:
                    raise NotImplementedError(
                        "Deleting steps outside of a proof is not implemented yet"
                    )

                proof, i = optional
                self._delete_step(change.step_index, in_proof=True, validate_file=False)
                proof.steps.pop(i)
                offset_steps -= 1
            else:
                raise NotImplementedError(f"Unknown change: {change}")

            for e in range(i, len(proof.steps)):
                # The goals will be loaded if used (Lazy Loading)
                proof.steps[e].goals = self._goals

        if len(self.steps) != previous_steps_size + offset_steps or not self.is_valid:
            raise InvalidChangeException()

    def close(self):
        """Closes all resources used by this object."""
        super().close()
        self.__aux_file.close()
