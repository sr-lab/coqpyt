import os
import hashlib
import tempfile
import shutil
import uuid
from typing import Optional, Tuple, List, Dict

from coqpyt.lsp.structs import (
    TextDocumentItem,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    ResponseError,
    ErrorCodes,
)
from coqpyt.coq.lsp.structs import Result, Query, Range, GoalAnswer, Position
from coqpyt.coq.lsp.client import CoqLspClient
from coqpyt.coq.structs import TermType, Step, Term, ProofStep, ProofTerm
from coqpyt.coq.exceptions import *
from coqpyt.coq.changes import *
from coqpyt.coq.context import FileContext
from coqpyt.coq.base_file import CoqFile


_ProofTerm: Tuple[Term, List[Term], List[ProofStep], Optional[Term]]


class _AuxFile(object):
    __CACHE: Dict[Tuple[str, str], FileContext] = {}

    def __init__(
        self,
        file_path,
        copy: bool = False,
        workspace: Optional[str] = None,
        timeout: int = 30,
    ):
        self.__copy = copy
        self.__init_path(file_path)
        if workspace is not None:
            uri = f"file://{workspace}"
        else:
            uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path):
        new_path = os.path.join(
            os.path.dirname(file_path),
            "coqpyt_aux_" + str(uuid.uuid4()).replace("-", "") + ".v",
        )
        with open(new_path, "w"):
            # Create empty file
            pass

        if self.__copy:
            shutil.copyfile(file_path, new_path)

        self.path = new_path
        self.version = 1

    def __handle_exception(self, e):
        if not isinstance(e, ResponseError) or e.code not in [
            ErrorCodes.ServerQuit.value,
            ErrorCodes.ServerTimeout.value,
        ]:
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        os.remove(self.path)

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

    def read(self):
        with open(self.path, "r") as f:
            return f.read()

    def write(self, text):
        with open(self.path, "w") as f:
            f.write(text)

    def append(self, text):
        with open(self.path, "a") as f:
            f.write(text)

    def truncate(self, text):
        text = text.encode("utf-8")
        with open(self.path, "rb+") as f:
            # We find the last occurrence of text and truncate everything after it
            file_content = f.read()
            f.seek(-(len(file_content) - file_content.rfind(text)), os.SEEK_END)
            f.truncate()

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

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.path)

    @staticmethod
    def get_library(
        library_name: str, library_file: str, timeout: int
    ) -> Dict[str, Term]:
        with open(library_file, "r") as f:
            hash = hashlib.md5(f.read().encode("utf-8")).hexdigest()
        if (library_file, hash) in _AuxFile.__CACHE:
            aux_context = _AuxFile.__CACHE[(library_file, hash)]
        else:
            coq_file = CoqFile(library_file, library=library_name, timeout=timeout)
            coq_file.run()
            aux_context = coq_file.context
            _AuxFile.__CACHE[(library_file, hash)] = aux_context
            coq_file.close()

        # FIXME: we ignore the usage of "Local" from imported files to
        # simplify the implementation. However, they can be used:
        # https://coq.inria.fr/refman/language/core/modules.html?highlight=local#coq:attr.local
        # NOTE: We handle "Local" separately from section-local keywords
        # due to the aforementioned reason. The handling should be different
        # for both types of keywords.
        terms = aux_context.terms
        for term in aux_context.terms.keys():
            if terms[term].text.startswith("Local"):
                terms.pop(term)
        return terms

    @staticmethod
    def get_libraries(aux_file: "_AuxFile") -> List[str]:
        aux_file.append("\nPrint Libraries.")
        aux_file.didChange()

        last_line = len(aux_file.read().split("\n")) - 1
        libraries = aux_file.get_diagnostics("Print Libraries", "", last_line)
        aux_file.truncate("\nPrint Libraries.")
        return list(map(lambda line: line.strip(), libraries.split("\n")[1:-1]))

    @staticmethod
    def get_coq_context(timeout: int) -> FileContext:
        temp_path = os.path.join(
            tempfile.gettempdir(), "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )

        with _AuxFile(file_path=temp_path, timeout=timeout) as aux_file:
            aux_file.didOpen()
            libraries = _AuxFile.get_libraries(aux_file)
            for library in libraries:
                aux_file.append(f"\nLocate Library {library}.")
            aux_file.didChange()

            context = FileContext(temp_path)
            for i, library in enumerate(libraries):
                v_file = aux_file.get_diagnostics(
                    "Locate Library", library, i + 1
                ).split()[-1][:-1]
                terms = _AuxFile.get_library(library, v_file, timeout)
                context.add_library(library, terms)

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
        self.__aux_file = _AuxFile(file_path, timeout=self.timeout, workspace=workspace)
        self.__aux_file.didOpen()

        try:
            # We need to update the context already defined in the CoqFile
            self.context.update(_AuxFile.get_coq_context(self.timeout))
        except Exception as e:
            self.close()
            raise e

        self.__program_context: Dict[str, Tuple[Term, List[Term]]] = {}
        self.__proofs: List[ProofTerm] = []
        self.__open_proofs: List[_ProofTerm] = []
        self.__last_end_pos: Optional[Position] = None
        self.__current_goals = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __locate(self, search, line):
        nots = self.__aux_file.get_diagnostics("Locate", f'"{search}"', line).split(
            "\n"
        )
        fun = lambda x: x.endswith("(default interpretation)")
        return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __step_context(self, step: Step) -> List[Term]:
        stack, res = self.context.expr(step)[:0:-1], []
        while len(stack) > 0:
            el = stack.pop()
            if isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                term = self.context.get_term(FileContext.get_id(el))
                if term is not None and term not in res:
                    res.append(term)
            elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                line = len(self.__aux_file.read().split("\n"))
                self.__aux_file.append(f'\nLocate "{el[2][1]}".')
                self.__aux_file.didChange()

                notation_name, scope = el[2][1], ""
                notation = self.__locate(notation_name, line)
                if notation.split(":")[-1].endswith("_scope"):
                    scope = notation.split(":")[-1].strip()

                if notation != "Unknown notation":
                    term = self.context.get_notation(notation_name, scope)
                    if term not in res:
                        res.append(term)

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

    def __get_program_context(self) -> Tuple[Term, List[Term]]:
        expr = self.context.expr(self.prev_step)
        # Tags:
        # 0 - Obligation N of id : type
        # 1 - Obligation N of id
        # 2 - Obligation N : type
        # 3 - Obligation N
        # 4 - Next Obligation of id
        # 5 - Next Obligation
        tag = expr[1][1]
        if tag in [0, 1, 4]:
            stack = expr[:0:-1]
            while len(stack) > 0:
                el = stack.pop()
                if not isinstance(el, list):
                    continue

                ident = FileContext.get_ident(el)
                if ident is not None:
                    # This works because the obligation must be in the
                    # same module as the program
                    id = self.context.append_module_prefix(ident)
                    return self.__program_context[id]

                for v in reversed(el):
                    if isinstance(v, list):
                        stack.append(v)
        elif tag in [2, 3, 5]:
            id = self.current_goals.program[0][0][1]
            # This works because the obligation must be in the
            # same module as the program
            id = self.context.append_module_prefix(id)
            return self.__program_context[id]
        text = self.context.last_term.text
        raise RuntimeError(f"Unknown obligation command with tag number {tag}: {text}")

    def __check_program(self):
        goals = self.current_goals
        if len(goals.program) == 0:
            return
        id = self.context.append_module_prefix(goals.program[-1][0][1])
        if id in self.__program_context:
            return
        self.__program_context[id] = (
            self.context.last_term,
            self.__step_context(self.prev_step),
        )

    def __handle_end_proof(
        self,
        step: Step,
        goals: Optional[GoalAnswer],
        index: Optional[int] = None,
        open_index: Optional[int] = None,
    ):
        if goals is None:
            index = -1 if index is None else index
            open_index = len(self.__open_proofs) if open_index is None else open_index
            proof = self.__proofs.pop(index)
            self.__open_proofs.insert(
                open_index, (proof, proof.context, proof.steps[:-1], proof.program)
            )
        else:
            index = len(self.__proofs) if index is None else index
            open_index = -1 if open_index is None else open_index
            open_proof = self.__open_proofs.pop(open_index)
            open_proof[2].append(ProofStep(step, goals, []))
            self.__proofs.insert(index, ProofTerm(*open_proof))

    def __handle_proof_step(self, step: Step, goals: Optional[GoalAnswer]):
        if goals is None:
            self.__open_proofs[-1][2].pop()
        else:
            context = self.__step_context(step)
            self.__open_proofs[-1][2].append(ProofStep(step, goals, context))

    def __handle_proof_term(
        self, step: Step, goals: Optional[GoalAnswer], index: Optional[int] = None
    ):
        if goals is None:
            index = -1 if index is None else index
            self.__open_proofs.pop(index)
        else:
            index = len(self.__open_proofs) if index is None else index
            # New proof terms can be either obligations or regular proofs
            proof_term, program = self.context.last_term, None
            if self.context.term_type(step) == TermType.OBLIGATION:
                program, statement_context = self.__get_program_context()
            else:
                statement_context = self.__step_context(step)
            self.__open_proofs.insert(
                index, (proof_term, statement_context, [], program)
            )

    def __is_proof_term(self, step: Step):
        term_type = self.context.term_type(step)
        # Assume that terms of the following types do not introduce new proofs
        # FIXME: Should probably check if goals were changed
        return term_type not in [
            TermType.TACTIC,
            TermType.NOTATION,
            TermType.INDUCTIVE,
            TermType.COINDUCTIVE,
            TermType.RECORD,
            TermType.CLASS,
            TermType.SCHEME,
            TermType.VARIANT,
            TermType.OTHER,
        ]

    def __is_end_proof(self, step: Step):
        return self.context.expr(step)[0] in ["VernacEndProof", "VernacExactProof"]

    def __check_proof_step(self, step: Step, goals: Optional[GoalAnswer] = None):
        # Last step of the file
        if step.text.strip() == "":
            return

        # Found [Qed]/[Defined]/[Admitted] or [Proof <exact>.]
        if self.__is_end_proof(step):
            self.__handle_end_proof(step, goals)
        elif self.__is_proof_term(step):
            self.__handle_proof_term(step, goals)
        # Avoids Tactics, Notations, Inductive...
        elif self.context.term_type(step) == TermType.OTHER:
            self.__handle_proof_step(step, goals)

    def __forward_step(self, goals: GoalAnswer):
        self.__aux_file.append(self.prev_step.text)
        self.__check_program()
        if self.in_proof or self.__is_end_proof(self.prev_step):
            self.__check_proof_step(self.prev_step, goals)

    def __backward_step(self):
        self.__aux_file.truncate(self.curr_step.text)
        if len(self.open_proofs) > 0 or self.__is_end_proof(self.curr_step):
            self.__check_proof_step(self.curr_step)

    def __find_step(self, range: Range) -> Optional[Tuple[ProofTerm, int, int]]:
        for p, proof in enumerate(self.__proofs):
            if proof.ast.range == range:
                return (proof, p, -1)

            for i, proof_step in enumerate(proof.steps):
                if proof_step.ast.range == range:
                    return (proof, p, i)

        for p, proof in enumerate(self.__open_proofs):
            if proof[0].ast.range == range:
                # NOTE: This works because the change of the structures inside
                # will reflect on the open proof (e.g. list)
                return (ProofTerm(*proof), p, -1)

            for i, proof_step in enumerate(proof[2]):
                if proof_step.ast.range == range:
                    return (ProofTerm(*proof), p, i)

        return None

    def __get_step(self, step_index):
        self.__aux_file.write("")
        for step in self.steps[: step_index + 1]:
            self.__aux_file.append(step.text)
        self.__aux_file.didChange()
        context = self.__step_context(self.steps[step_index])

        # The goals will be loaded if used (Lazy Loading)
        goals = self.__goals
        return ProofStep(self.steps[step_index], goals, context)

    def __update_libraries(self):
        libraries = _AuxFile.get_libraries(self.__aux_file)
        # New libraries
        new_libraries = set(libraries) - set(self.context.libraries.keys())
        last_line = len(self.__aux_file.read().split("\n")) - 1
        for library in new_libraries:
            self.__aux_file.append(f"\nLocate Library {library}.")

        # The didChange is expensive so we only do it if needed
        if len(new_libraries) > 0:
            self.__aux_file.didChange()

        for i, library in enumerate(new_libraries):
            library_file = self.__aux_file.get_diagnostics(
                "Locate Library", library, last_line + i + 1
            ).split()[-1][:-1]
            library_terms = _AuxFile.get_library(library, library_file, self.timeout)
            self.context.add_library(library, library_terms)

        # Deleted libraries
        for library in set(self.context.libraries.keys()) - set(libraries):
            self.context.remove_library(library)

    def __find_open_proof_index(self, step: Step) -> int:
        for i, proof in enumerate(self.__open_proofs):
            if proof[0].step.ast.range > step.ast.range:
                return i
        return len(self.__open_proofs)

    def __find_proof_index(self, step: Step) -> int:
        for i, proof in enumerate(self.__proofs):
            if proof.step.ast.range > step.ast.range:
                return i
        return len(self.__proofs)

    def __goals(self, end_pos: Position):
        uri = f"file://{self._path}"
        try:
            return self.coq_lsp_client.proof_goals(TextDocumentIdentifier(uri), end_pos)
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def __in_proof(self, goals: Optional[GoalAnswer]):
        return goals is not None and goals.goals is not None

    def __can_close_proof(self, goals: Optional[GoalAnswer]):
        def empty_stack(stack):
            # e.g. [([], [])]
            for tuple in stack:
                if len(tuple[0]) > 0 or len(tuple[1]) > 0:
                    return False
            return True

        goals = goals.goals
        if goals is None:
            return False

        return (
            len(goals.goals) == 0
            and empty_stack(goals.stack)
            and len(goals.shelf) == 0
            and goals.bullet is None
        )

    @property
    def proofs(self) -> List[ProofTerm]:
        """Gets all the closed proofs in the file and their corresponding steps.

        Returns:
            List[ProofTerm]: Each element has the list of steps for a single
                closed proof of the Coq file. The proofs are ordered by the
                order they are closed on the file. The steps include the
                context used for each step and the goals in that step.
        """
        return self.__proofs

    @property
    def open_proofs(self) -> List[ProofTerm]:
        """Gets all the open proofs in the file and their corresponding steps.

        Returns:
            List[ProofTerm]: Each element has the list of steps for a single
                open proof of the Coq file. The proofs are ordered by the
                order they are opened on the file. The steps include the
                context used for each step and the goals in that step.
        """
        return [ProofTerm(*proof) for proof in self.__open_proofs]

    @property
    def current_goals(self) -> Optional[GoalAnswer]:
        """Get goals in current position.

        Returns:
            Optional[GoalAnswer]: Goals in the current position if there are goals.
        """
        if self.steps_taken == len(self.steps):
            end_pos = self.prev_step.ast.range.end
        else:
            end_pos = self.curr_step.ast.range.start

        if end_pos != self.__last_end_pos:
            self.__current_goals = self.__goals(end_pos)
            self.__last_end_pos = end_pos

        return self.__current_goals

    @property
    def in_proof(self) -> bool:
        """
        Returns:
            bool: True if the current step is inside a proof.
        """
        return self.__in_proof(self.current_goals)

    @property
    def can_close_proof(self):
        """
        Returns:
            bool: True if the next step can be a [Qed].
        """
        return self.__can_close_proof(self.current_goals)

    def exec(self, nsteps=1) -> List[Step]:
        sign = 1 if nsteps > 0 else -1
        initial_steps_taken = self.steps_taken
        nsteps = min(
            nsteps * sign,
            len(self.steps) - self.steps_taken if sign > 0 else self.steps_taken,
        )
        step = self.__forward_step if sign == 1 else lambda _: self.__backward_step()

        for _ in range(nsteps):
            try:
                goals = self.current_goals
            except Exception as e:
                self.__aux_file.close()
                raise e

            # HACK: We ignore steps inside a Module Type since they can't
            # be used outside and should be overriden.
            in_module_type = self.context.in_module_type
            self._step(sign)
            if in_module_type or self.context.in_module_type:
                continue
            step(goals)

            if (
                sign == 1
                and self.context.expr(self.prev_step)[0]
                in ["VernacRequire", "VernacImport"]
            ) or (
                sign == -1
                and self.context.expr(self.curr_step)[0]
                in ["VernacRequire", "VernacImport"]
            ):
                self.__update_libraries()

        last, slice = sign == 1, (initial_steps_taken, self.steps_taken)
        return self.steps[slice[1 - last] : slice[last]]

    def add_step(self, previous_step_index: int, step_text: str):
        steps = self.steps_taken - previous_step_index - 1
        offset = 1 if previous_step_index + 1 < self.steps_taken else 0

        optional = self.__find_step(self.steps[previous_step_index].ast.range)
        self._make_change(self._add_step, previous_step_index, step_text)

        # The step was not processed yet
        if self.steps_taken <= previous_step_index + 1:
            super().exec(steps + offset)
            return
        super().exec(-steps)

        # NOTE: We rollback so the last_term is the correct one
        # We use the CoqFile is exec because it is faster
        super().exec(1)
        # Allows to add open proofs
        step = self.steps[previous_step_index + 1]
        if self.__is_proof_term(step):
            goals = self.__goals(step.ast.range.end)
            if self.__in_proof(goals):
                index = self.__find_open_proof_index(step)
                self.__handle_proof_term(step, goals, index=index)
        # Handles case where Qed is added
        elif self.__is_end_proof(step):
            # This is not outside of the ifs for performance reasons
            goals = self.__goals(step.ast.range.end)
            index = self.__find_proof_index(step)
            open_index = self.__find_open_proof_index(step) - 1
            self.__handle_end_proof(step, goals, index=index, open_index=open_index)
        # Regular proof steps
        elif optional is not None:
            proof, _, prev = optional
            proof.steps.insert(prev + 1, self.__get_step(previous_step_index + 1))
            # We should change the goals of all the steps in the same proof
            # after the one that was changed
            # NOTE: We assume the proofs and steps are in the order they are written
            for e in range(prev + 2, len(proof.steps)):
                # The goals will be loaded if used (Lazy Loading)
                proof.steps[e].goals = self.__goals
        super().exec(steps + offset - 1)

    def delete_step(self, step_index: int) -> None:
        step = self.steps[step_index]
        optional = self.__find_step(step.ast.range)

        self._make_change(self._delete_step, step_index)
        # The step was not processed yet
        if self.steps_taken <= step_index:
            return

        # Handles case where Qed is deleted
        elif self.__is_end_proof(step):
            index = self.__find_proof_index(step) - 1
            open_index = self.__find_open_proof_index(step)
            self.__handle_end_proof(step, None, index=index, open_index=open_index)
        # Handle regular proof steps
        elif optional is not None:
            proof, proof_index, i = optional
            if i == -1:
                # The proof was deleted
                self.__handle_proof_term(step, None, index=proof_index)
            else:
                proof.steps.pop(i)
                for e in range(i, len(proof.steps)):
                    # The goals will be loaded if used (Lazy Loading)
                    proof.steps[e].goals = self.__goals

    def change_steps(self, changes: List[CoqChange]):
        min_step = self.steps_taken
        offset = self._get_steps_taken_offset(changes)

        for change in changes:
            if isinstance(change, CoqAddStep):
                min_step = min(min_step, change.previous_step_index)
            elif isinstance(change, CoqDeleteStep):
                min_step = min(min_step, change.step_index)
        steps = self.steps_taken - min_step

        self.exec(-steps)
        super().change_steps(changes)
        self.exec(steps + offset)

    def close(self):
        super().close()
        self.__aux_file.close()
