import os
import shutil
import uuid
import tempfile
from typing import Optional, List

from coqpyt.lsp.structs import (
    TextDocumentItem,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    ResponseError,
    ErrorCodes,
    Diagnostic,
)
from coqpyt.coq.lsp.structs import Position, GoalAnswer, RangedSpan, Range
from coqpyt.coq.lsp.client import CoqLspClient
from coqpyt.coq.exceptions import *
from coqpyt.coq.changes import *
from coqpyt.coq.structs import Step
from coqpyt.coq.context import FileContext


class CoqFile(object):
    """Abstraction to interact with a Coq file

    Attributes:
        coq_lsp_client (CoqLspClient): coq-lsp client used on the file
        ast (List[RangedSpan]): AST of the Coq file. Each element is a step
            of execution in the Coq file.
        steps_taken (int): The number of steps already executed
        context (FileContext): The context defined in the file.
        path (str): Path of the file. If the file is from the Coq library, a
            temporary file will be used.
        file_module(List[str]): Module where the file is included.
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
        """Creates a CoqFile.

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
        self.__init_path(file_path, library)

        if workspace is not None:
            uri = f"file://{workspace}"
        else:
            uri = f"file://{self.__path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout, coq_lsp=coq_lsp)
        uri = f"file://{self.__path}"
        text = self.__read()

        try:
            self.coq_lsp_client.didOpen(TextDocumentItem(uri, "coq", 1, text))
            ast = self.coq_lsp_client.get_document(TextDocumentIdentifier(uri)).spans
        except Exception as e:
            self.__handle_exception(e)
            raise e

        self.steps_taken: int = 0
        self.__init_steps(text, ast)
        self.__validate()
        self.context = FileContext(self.path, module=self.file_module, coqtop=coqtop)
        self.version = 1
        self.__last_end_pos: Optional[Position] = None
        self.__current_goals = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path, library):
        self.file_module = [] if library is None else library.split(".")
        self.__from_lib = self.file_module[:2] == ["Coq", "Init"]
        self.path = file_path
        if not self.__from_lib:
            self.__path = file_path
            return

        # Coq LSP cannot open files from Coq library, so we need to work with
        # a copy of such files.
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "coq_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)
        self.__path = new_path

    def __handle_exception(self, e):
        if not isinstance(e, ResponseError) or e.code not in [
            ErrorCodes.ServerQuit.value,
            ErrorCodes.ServerTimeout.value,
        ]:
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self.__path)

    def __init_step(
        self,
        lines: List[str],
        index: int,
        step_ast: RangedSpan,
        prev_step_ast: RangedSpan,
    ):
        start_line = 0 if index == 0 else prev_step_ast.range.end.line
        start_char = 0 if index == 0 else prev_step_ast.range.end.character
        end_line = step_ast.range.end.line
        end_char = step_ast.range.end.character

        curr_lines = lines[start_line : end_line + 1]
        curr_lines[-1] = curr_lines[-1][:end_char]
        curr_lines[0] = curr_lines[0][start_char:]
        step_text = "\n".join(curr_lines)

        if index == 0:
            short_text = self.__short_text(step_text, step_ast)
        else:
            short_text = self.__short_text(step_text, step_ast, prev_step_ast)

        return Step(step_text, short_text, step_ast)

    def __init_steps(self, text: str, ast: List[RangedSpan]):
        lines = text.split("\n")
        self.steps: List[Step] = []
        for i, curr_ast in enumerate(ast):
            self.steps.append(self.__init_step(lines, i, curr_ast, ast[i - 1]))

    def __validate(self):
        uri = f"file://{self.__path}"
        self.is_valid = True
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return

        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            if diagnostic.severity == 1:
                self.is_valid = False

            for step in self.steps:
                if (
                    step.ast.range.start <= diagnostic.range.start
                    and step.ast.range.end >= diagnostic.range.end
                ):
                    step.diagnostics.append(diagnostic)
                    break

    def __short_text(
        self, text: str, curr_step: RangedSpan, prev_step: Optional[RangedSpan] = None
    ):
        curr_range = curr_step.range
        nlines = curr_range.end.line - curr_range.start.line + 1
        lines = text.split("\n")[-nlines:]

        start = curr_range.start.character
        if prev_step is not None and prev_step.range.end.line >= curr_range.start.line:
            start -= prev_step.range.end.character

        lines[-1] = lines[-1][: curr_range.end.character]
        lines[0] = lines[0][start:]

        return " ".join(" ".join(lines).split())

    def __read(self):
        with open(self.path, "r") as f:
            return f.read()

    def _goals(self, end_pos: Position):
        uri = f"file://{self.__path}"
        try:
            return self.coq_lsp_client.proof_goals(TextDocumentIdentifier(uri), end_pos)
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def _can_close_proof(self, goals: Optional[GoalAnswer]):
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

    def __in_proof(self, goals: Optional[GoalAnswer]):
        return goals is not None and goals.goals is not None

    def __update_steps(self):
        uri = f"file://{self.path}"
        text = self.__read()
        try:
            self.version += 1
            self.coq_lsp_client.didChange(
                VersionedTextDocumentIdentifier(uri, self.version),
                [TextDocumentContentChangeEvent(None, None, text)],
            )
            ast = self.coq_lsp_client.get_document(TextDocumentIdentifier(uri)).spans
        except Exception as e:
            self.__handle_exception(e)
            raise e
        self.__init_steps(text, ast)
        self.__validate()

    def _step(self, sign):
        if sign == 1:
            self.context.process_step(self.curr_step)
        else:
            self.context.undo_step(self.prev_step)
        self.steps_taken += sign

    def _make_change(self, change_function, *args):
        previous_steps = self.steps
        old_steps_taken = self.steps_taken
        old_diagnostics = self.coq_lsp_client.lsp_endpoint.diagnostics
        lines = self.__read().split("\n")
        old_text = "\n".join(lines)

        try:
            change_function(*args)
        except InvalidChangeException as e:
            # Rollback changes
            self.steps = previous_steps
            self.steps_taken = old_steps_taken
            self.coq_lsp_client.lsp_endpoint.diagnostics = old_diagnostics
            self.is_valid = True
            with open(self.path, "w") as f:
                f.write(old_text)
            raise e
        
    def __delete_step_text(self, step_index: int):
        with open(self.__path, "r") as f:
            lines = f.readlines()

        deleted_step = self.steps[step_index]
        step = deleted_step
        prev_step = self.steps[step_index - 1]
        start_line = lines[prev_step.ast.range.end.line]
        end_line = lines[step.ast.range.end.line]

        start_line = start_line[: prev_step.ast.range.end.character]
        end_line = end_line[step.ast.range.end.character :]

        if prev_step.ast.range.end.line == step.ast.range.end.line:
            lines[prev_step.ast.range.end.line] = start_line + end_line
        else:
            lines[prev_step.ast.range.end.line] = start_line
            lines[step.ast.range.end.line] = end_line

        # Delete lines between first and last line
        for i in range(prev_step.ast.range.end.line + 1, step.ast.range.end.line):
            del lines[i]
        text = "".join(lines)

        with open(self.__path, "w") as f:
            f.write(text)

    def __add_step_text(self, previous_step_index: int, step_text: str):
        with open(self.__path, "r") as f:
            lines = f.readlines()

        previous_step = self.steps[previous_step_index]
        end_line = lines[previous_step.ast.range.end.line]
        end_line = end_line[: previous_step.ast.range.end.character] + step_text + end_line[previous_step.ast.range.end.character :]
        lines[previous_step.ast.range.end.line] = end_line

        text = "".join(lines)

        with open(self.__path, "w") as f:
            f.write(text)

    def __delete_update_ast(self, step_index: int):
        deleted_step = self.steps[step_index]
        for step in self.steps[step_index + 1 :]:
            remove_chars = deleted_step.ast.range.end.character
            if deleted_step.ast.range.end.line == deleted_step.ast.range.start.line:
                remove_chars -= deleted_step.ast.range.start.character - 1

            if step.ast.range.start.line == deleted_step.ast.range.end.line:
                step.ast.range.start.character -= remove_chars
            if step.ast.range.end.line == deleted_step.ast.range.end.line:
                step.ast.range.end.character -= remove_chars

            step.ast.range.start.line -= deleted_step.text.count("\n")
            step.ast.range.end.line -= deleted_step.text.count("\n")

    def __add_update_ast(self, previous_step_index: int, step_text: str) -> Step:
        previous_step = self.steps[previous_step_index]

        newline_start = len(step_text) - len(step_text.lstrip("\n"))
        if newline_start > 0:
            start_line = previous_step.ast.range.end.line + newline_start
            start_char = 0
        else:
            start_line = previous_step.ast.range.end.line
            start_char = previous_step.ast.range.end.character + len(step_text) - len(step_text.lstrip())

        end_line = start_line + step_text.count("\n")
        if start_line == end_line:
            end_char = start_char + len(step_text.split("\n")[-1])
        else:
            end_char = len(step_text.split("\n")[-1])

        # We will create a placeholder step that will be replaced later
        added_step = Step(step_text, step_text, RangedSpan(Range(
            Position(start_line, start_char),
            Position(start_line, end_char)
        ),None))

        for i, step in enumerate(self.steps[previous_step_index + 1 :]):
            add_chars = added_step.ast.range.end.character
            if added_step.ast.range.start.line == added_step.ast.range.start.line:
                add_chars -= added_step.ast.range.start.character

            step.ast.range.start.line += step_text.count("\n")
            step.ast.range.end.line += step_text.count("\n")

            if step.ast.range.start.line == added_step.ast.range.end.line:
                step.ast.range.start.character += add_chars
            if step.ast.range.end.line == added_step.ast.range.end.line:
                step.ast.range.end.character += add_chars

        return added_step

    def _delete_step(
        self,
        step_index: int,
        validate_file: bool = True,
    ) -> None:
        # FIXME remove calls to in_proof in delete_step and add_step
        self.__delete_step_text(step_index)

        # Modify the previous steps instead of creating new ones
        # This is important to preserve their references
        # For instance, in the ProofFile
        previous_steps = self.steps
        self.__update_steps()

        if validate_file and (
            # We will remove the step from the previous steps
            len(self.steps) != len(previous_steps) - 1
            or not self.is_valid
        ):
            raise InvalidDeleteException(self.steps[step_index].text)

        deleted_step = previous_steps.pop(step_index)
        for i, step in enumerate(previous_steps):
            step.text, step.ast = self.steps[i].text, self.steps[i].ast
            step.diagnostics = self.steps[i].diagnostics
        self.steps = previous_steps

        if self.steps_taken > step_index:
            self.steps_taken -= 1
            n_steps = step_index - self.steps_taken
            # We don't use self to avoid calling method of ProofFile
            CoqFile.exec(self, n_steps)
            self.context.undo_step(deleted_step)
            CoqFile.exec(self, -n_steps)

    def _add_step(
        self,
        previous_step_index: int,
        step_text: str,
        validate_file: bool = True,
    ) -> None:
        # FIXME suffers from same problem when adding incorrect steps
        if validate_file and not self.is_valid:
            raise InvalidFileException(self.path)

        self.__add_step_text(previous_step_index, step_text)

        # Modify the previous steps instead of creating new ones
        # This is important to preserve their references
        # For instance, in the ProofFile
        previous_steps = self.steps
        step_index = previous_step_index + 1

        self.__update_steps()

        if validate_file and (
            # We will add the new step to the previous_steps
            len(self.steps) != len(previous_steps) + 1
            or self.steps[step_index].ast.span is None
            or not self.is_valid
        ):
            raise InvalidStepException(step_text)

        previous_steps.insert(step_index, self.steps[step_index])
        for i, step in enumerate(previous_steps):
            step.text, step.ast = self.steps[i].text, self.steps[i].ast
            step.diagnostics = self.steps[i].diagnostics
        self.steps = previous_steps

        if self.steps_taken - 1 > previous_step_index:
            self.steps_taken += 1
            n_steps = step_index - self.steps_taken
            CoqFile.exec(self, n_steps + 1)
            # Ignore step when going back
            self.steps_taken -= 1
            CoqFile.exec(self, -n_steps)

    def _get_steps_taken_offset(self, changes: List[CoqChange]):
        offset = 0
        steps_taken = self.steps_taken

        for change in changes:
            if isinstance(change, CoqAddStep):
                if change.previous_step_index < steps_taken:
                    offset += 1
                    steps_taken += 1
            elif isinstance(change, CoqDeleteStep):
                if change.step_index < steps_taken:
                    offset -= 1
                    steps_taken -= 1

        return offset

    def _change_steps(self, changes: List[CoqChange]):
        CoqFile.exec(self, -self.steps_taken)
        offset_steps = 0
        offset_steps_taken = self._get_steps_taken_offset(changes)
        previous_steps = self.steps
        previous_steps_size = len(self.steps)

        for change in changes:
            if isinstance(change, CoqAddStep):
                self.__add_step_text(change.previous_step_index, change.step_text)
                step = self.__add_update_ast(change.previous_step_index, change.step_text)
                self.steps.insert(change.previous_step_index + 1, step)
                offset_steps += 1
            elif isinstance(change, CoqDeleteStep):
                self.__delete_step_text(change.step_index)
                self.__delete_update_ast(change.step_index)
                self.steps.pop(change.step_index)
                offset_steps -= 1
            else:
                raise NotImplementedError(f"Unknown change: {change}")

        self.__update_steps()
        if len(self.steps) != previous_steps_size + offset_steps or not self.is_valid:
            raise InvalidChangeException()

        for i, step in enumerate(previous_steps):
            step.text, step.ast = self.steps[i].text, self.steps[i].ast
            # FIXME short text
            step.diagnostics = self.steps[i].diagnostics
        self.steps = previous_steps
        CoqFile.exec(self, self.steps_taken + offset_steps_taken)

    @property
    def curr_step(self):
        """
        Returns:
            Step: The next step to be executed.
        """
        return self.steps[self.steps_taken]

    @property
    def prev_step(self):
        """
        Returns:
            Step: The previously executed step.
        """
        return self.steps[self.steps_taken - 1]

    @property
    def timeout(self) -> int:
        """The timeout of the coq-lsp client.

        Returns:
            int: Timeout.
        """
        return self.coq_lsp_client.lsp_endpoint.timeout

    @property
    def checked(self) -> bool:
        """
        Returns:
            bool: True if the whole file was already executed
        """
        return self.steps_taken == len(self.steps)

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
            self.__current_goals = self._goals(end_pos)
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
        return self._can_close_proof(self.current_goals)

    @property
    def diagnostics(self) -> List[Diagnostic]:
        """
        Returns:
            List[Diagnostic]: The diagnostics of the file.
                Includes all messages given by Coq.
        """
        uri = f"file://{self.__path}"
        return self.coq_lsp_client.lsp_endpoint.diagnostics[uri]

    def exec(self, nsteps=1) -> List[Step]:
        """Execute steps in the file.

        Args:
            nsteps (int, optional): Number of steps to execute. Defaults to 1.

        Returns:
            List[Step]: List of steps executed.
        """
        sign = 1 if nsteps > 0 else -1
        initial_steps_taken = self.steps_taken
        nsteps = min(
            nsteps * sign,
            len(self.steps) - self.steps_taken if sign > 0 else self.steps_taken,
        )

        for _ in range(nsteps):
            self._step(sign)

        last, slice = sign == 1, (initial_steps_taken, self.steps_taken)
        return self.steps[slice[1 - last] : slice[last]]

    def run(self) -> List[Step]:
        """Executes the remaining steps in the file.

        Returns:
            List[Step]: List of the remaining steps in the file.
        """
        return self.exec(len(self.steps) - self.steps_taken)

    def delete_step(self, step_index: int) -> None:
        """Deletes a step from the file. The step must be inside a proof.
        This function will change the original file.

        Args:
            step_index (int): The index of the step to remove.

        Raises:
            NotImplementedError: If the step is outside a proof.
        """
        self._make_change(self._delete_step, step_index)

    def add_step(
        self,
        previous_step_index: int,
        step_text: str,
    ) -> None:
        """Adds a step to the file. The step must be inside a proof.
        This function will change the original file. If an exception is thrown
        the file will not be changed.

        Args:
            previous_step_index (int): The index of the previous step of the new step.
            step_text (str): The text of the step to add.

        Raises:
            NotImplementedError: If the step added is not on a proof.
            InvalidFileException: If the file being changed is not valid.
            InvalidStepException: If the step added is not valid.
        """
        self._make_change(self._add_step, previous_step_index, step_text)

    def change_steps(self, changes: List[CoqChange]):
        """Changes the steps of the Coq file transactionally.

        Args:
            changes (List[CoqChange]): The changes to be applied to the Coq file.
        """
        self._make_change(self._change_steps, changes)

    def save_vo(self):
        """Compiles the vo file for this Coq file."""
        uri = f"file://{self.__path}"
        try:
            self.coq_lsp_client.save_vo(TextDocumentIdentifier(uri))
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def close(self):
        """Closes all resources used by this object."""
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self.__path)
