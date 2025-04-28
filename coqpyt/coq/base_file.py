import os
import shutil
import uuid
import tempfile
from copy import deepcopy
from typing import Optional, List, Tuple

from coqpyt.lsp.structs import (
    TextDocumentItem,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
    ResponseError,
    ErrorCodes,
    Diagnostic,
)
from coqpyt.coq.lsp.structs import Position, RangedSpan, Range
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
        coq_lsp_options: Tuple[str] = None,
        coqtop: str = "coqtop",
    ):
        """Creates a CoqFile.

        Args:
            file_path (str): Path of the Coq file.
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
        if not os.path.isabs(file_path):
            file_path = os.path.abspath(file_path)
        self.__init_path(file_path, library)

        if workspace is not None:
            uri = f"file://{workspace}"
        else:
            uri = f"file://{self._path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout, coq_lsp_options=coq_lsp_options, coq_lsp=coq_lsp)
        uri = f"file://{self._path}"
        text = self.__read()

        try:
            self.coq_lsp_client.didOpen(TextDocumentItem(uri, "coq", 1, text))
            ast = self.coq_lsp_client.get_document(TextDocumentIdentifier(uri)).spans
        except Exception as e:
            self._handle_exception(e)
            raise e

        self.steps_taken: int = 0
        self.__init_steps(text, ast)
        self.__validate()
        self.context = FileContext(self.path, module=self.file_module, coqtop=coqtop)
        self.version = 1
        self.workspace = workspace

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path, library):
        self.file_module = [] if library is None else library.split(".")
        self.__from_lib = self.file_module[:2] == ["Coq", "Init"]
        self.path = file_path
        if not self.__from_lib:
            self._path = file_path
            return

        # Coq LSP cannot open files from Coq library, so we need to work with
        # a copy of such files.
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "coq_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)
        self._path = new_path

    def _handle_exception(self, e):
        if not isinstance(e, ResponseError) or e.code not in [
            ErrorCodes.ServerQuit.value,
            ErrorCodes.ServerTimeout.value,
        ]:
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self._path)

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
        # NOTE: We remove the last step if it is an empty step
        if ast[-1].span == None:
            ast = ast[:-1]
        for i, curr_ast in enumerate(ast):
            self.steps.append(self.__init_step(lines, i, curr_ast, ast[i - 1]))

    def __validate(self):
        uri = f"file://{self._path}"
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

    def __refresh(self):
        uri = f"file://{self.path}"
        text = self.__read()
        try:
            self.version += 1
            self.coq_lsp_client.didChange(
                VersionedTextDocumentIdentifier(uri, self.version),
                [TextDocumentContentChangeEvent(None, None, text)],
            )
        except Exception as e:
            self._handle_exception(e)
            raise e

    def __update_steps(self):
        self.__refresh()
        uri = f"file://{self.path}"
        text = self.__read()
        try:
            ast = self.coq_lsp_client.get_document(TextDocumentIdentifier(uri)).spans
        except Exception as e:
            self._handle_exception(e)
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
        uri = f"file://{self._path}"
        if not self.is_valid:
            raise InvalidFileException(self.path)

        self.__set_backup_steps()
        old_steps_taken = self.steps_taken
        old_diagnostics = self.coq_lsp_client.lsp_endpoint.diagnostics[uri]
        self.coq_lsp_client.lsp_endpoint.diagnostics[uri] = []
        old_text = self.__read()

        try:
            change_function(*args)
        except InvalidChangeException as e:
            # Rollback changes
            self.steps = self.__backup_steps
            self.steps_taken = old_steps_taken
            self.is_valid = True
            with open(self.path, "w") as f:
                f.write(old_text)
            e.diagnostics = self.coq_lsp_client.lsp_endpoint.diagnostics[uri]
            self.__refresh()
            self.coq_lsp_client.lsp_endpoint.diagnostics[uri] = old_diagnostics
            raise e

    def __delete_step_text(self, step_index: int):
        with open(self._path, "r") as f:
            lines = f.readlines()

        step = self.steps[step_index]
        if step_index != 0:
            prev_step_end = self.steps[step_index - 1].ast.range.end
        else:
            prev_step_end = Position(0, 0)

        start_line = lines[prev_step_end.line]
        end_line = lines[step.ast.range.end.line]

        end_line = end_line[step.ast.range.end.character :]
        start_line = start_line[: prev_step_end.character]

        if prev_step_end.line == step.ast.range.end.line:
            lines[prev_step_end.line] = start_line + end_line
        else:
            lines[prev_step_end.line] = start_line
            lines[step.ast.range.end.line] = end_line

        # Delete lines between first and last line
        for _ in range(step.ast.range.end.line - prev_step_end.line - 1):
            del lines[prev_step_end.line + 1]
        text = "".join(lines)

        with open(self._path, "w") as f:
            f.write(text)

    def __add_step_text(self, previous_step_index: int, step_text: str):
        with open(self._path, "r") as f:
            lines = f.readlines()

        previous_step = self.steps[previous_step_index]
        end_line = lines[previous_step.ast.range.end.line]
        end_line = (
            end_line[: previous_step.ast.range.end.character]
            + step_text
            + end_line[previous_step.ast.range.end.character :]
        )
        lines[previous_step.ast.range.end.line] = end_line

        text = "".join(lines)

        with open(self._path, "w") as f:
            f.write(text)

    def __delete_update_ast(self, step_index: int):
        deleted_step = self.steps[step_index]
        if step_index != 0:
            prev_step_end = self.steps[step_index - 1].ast.range.end
        else:
            prev_step_end = Position(0, 0)

        deleted_lines = deleted_step.text.count("\n")
        last_line_chars = deleted_step.ast.range.end.character
        last_line_offset = 0
        if deleted_step.ast.range.start.line == prev_step_end.line:
            last_line_chars -= prev_step_end.character
        else:
            last_line_offset = prev_step_end.character

        for step in self.steps[step_index:]:
            step.ast.range.start.line -= deleted_lines
            step.ast.range.end.line -= deleted_lines

            if step.ast.range.start.line == deleted_step.ast.range.end.line:
                step.ast.range.start.character -= last_line_chars - last_line_offset
            if step.ast.range.end.line == deleted_step.ast.range.end.line:
                step.ast.range.end.character -= last_line_chars - last_line_offset

    def __add_update_ast(self, previous_step_index: int, step_text: str) -> Step:
        prev_step_end = self.steps[previous_step_index].ast.range.end
        start = Position(prev_step_end.line, prev_step_end.character)

        added_lines = step_text.count("\n")
        end_char = last_line_chars = len(step_text.split("\n")[-1])
        if added_lines == 0:
            end_char += start.character
        end = Position(start.line + added_lines, end_char)

        # We will create a placeholder step that will be replaced later
        added_step = Step(step_text, step_text, RangedSpan(Range(start, end), None))

        for step in self.steps[previous_step_index + 1 :]:
            step.ast.range.start.line += added_lines
            step.ast.range.end.line += added_lines

            if step.ast.range.start.line == added_step.ast.range.end.line:
                step.ast.range.start.character += last_line_chars
            if step.ast.range.end.line == added_step.ast.range.end.line:
                step.ast.range.end.character += last_line_chars

        return added_step

    def __copy_steps(self):
        for i, step in enumerate(self.steps):
            index = self.__index_tracker[i]
            if index is None:  # Newly added steps
                continue

            backup = self.__backup_steps[index]
            backup.text, backup.ast = step.text, step.ast
            backup.diagnostics = step.diagnostics
            backup.short_text = step.short_text
            self.steps[i] = backup

    def __set_backup_steps(self):
        self.__backup_steps = self.steps[:]
        self.__index_tracker: List[Optional[int]] = []
        for i, step in enumerate(self.__backup_steps):
            self.steps[i] = deepcopy(step)
            self.__index_tracker.append(i)

    def _delete_step(self, step_index: int) -> None:
        deleted_step = self.steps[step_index]
        deleted_text = deleted_step.text
        self.__delete_step_text(step_index)

        # Modify the previous steps instead of creating new ones
        # This is important to preserve their references
        # For instance, in the ProofFile
        self.__update_steps()

        if not self.is_valid:
            raise InvalidDeleteException(deleted_text)

        # We will remove the step from the previous steps
        self.__index_tracker.pop(step_index)
        self.__copy_steps()

        if self.steps_taken > step_index:
            self.steps_taken -= 1
            n_steps = self.steps_taken - step_index
            # We don't use self to avoid calling method of ProofFile
            CoqFile.exec(self, -n_steps)
            self.context.undo_step(deleted_step)
            CoqFile.exec(self, n_steps)

    def _add_step(self, previous_step_index: int, step_text: str) -> None:
        self.__add_step_text(previous_step_index, step_text)

        # Modify the previous steps instead of creating new ones
        # This is important to preserve their references
        # For instance, in the ProofFile
        previous_steps_size = len(self.steps)
        step_index = previous_step_index + 1
        self.__update_steps()

        # NOTE: We check if exactly 1 step was added, because the text might contain
        # two steps or something that might lead to similar unwanted behaviour.
        if len(self.steps) != previous_steps_size + 1 or not self.is_valid:
            raise InvalidAddException(step_text)

        # We will add the new step to the previous steps
        self.__index_tracker.insert(step_index, None)
        self.__copy_steps()

        if self.steps_taken > step_index:
            self.steps_taken += 1
            n_steps = self.steps_taken - step_index
            CoqFile.exec(self, -n_steps + 1)
            # Ignore step when going back
            self.steps_taken -= 1
            CoqFile.exec(self, n_steps)

    def _get_steps_taken_offset(self, changes: List[CoqChange]):
        offset = 0
        steps_taken = self.steps_taken

        for change in changes:
            if isinstance(change, CoqAdd):
                if change.previous_step_index + 1 < steps_taken:
                    offset += 1
                    steps_taken += 1
            elif isinstance(change, CoqDelete):
                if change.step_index < steps_taken:
                    offset -= 1
                    steps_taken -= 1

        return offset

    def __change_steps(self, changes: List[CoqChange]):
        previous_steps_takens = self.steps_taken
        offset_steps, offset_steps_taken = 0, self._get_steps_taken_offset(changes)
        previous_steps_size = len(self.steps)
        CoqFile.exec(self, -self.steps_taken)

        for change in changes:
            if isinstance(change, CoqAdd):
                self.__add_step_text(change.previous_step_index, change.step_text)
                step = self.__add_update_ast(
                    change.previous_step_index, change.step_text
                )
                self.steps.insert(change.previous_step_index + 1, step)
                self.__index_tracker.insert(change.previous_step_index + 1, None)
                offset_steps += 1
            elif isinstance(change, CoqDelete):
                self.__delete_step_text(change.step_index)
                self.__delete_update_ast(change.step_index)
                self.steps.pop(change.step_index)
                self.__index_tracker.pop(change.step_index)
                offset_steps -= 1
            else:
                raise NotImplementedError(f"Unknown change: {change}")

        self.__update_steps()
        # NOTE: We check the expected offset, because a given step text might contain
        # two steps or something that might lead to similar unwanted behaviour.
        if len(self.steps) != previous_steps_size + offset_steps or not self.is_valid:
            CoqFile.exec(self, previous_steps_takens + offset_steps_taken)
            raise InvalidChangeException()

        self.__copy_steps()
        CoqFile.exec(self, previous_steps_takens + offset_steps_taken)

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
    def diagnostics(self) -> List[Diagnostic]:
        """
        Returns:
            List[Diagnostic]: The diagnostics of the file.
                Includes all messages given by Coq.
        """
        uri = f"file://{self._path}"
        return self.coq_lsp_client.lsp_endpoint.diagnostics[uri]

    @property
    def errors(self) -> List[Diagnostic]:
        """
        Returns:
            List[Diagnostic]: The errors of the file.
                Includes all messages given by Coq with severity 1.
        """
        return list(filter(lambda x: x.severity == 1, self.diagnostics))

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
        """Deletes a step from the file. This function will change the original file.
        If an exception is thrown the file will not be changed.

        Args:
            step_index (int): The index of the step to remove.

        Raises:
            InvalidFileException: If the file being changed is not valid.
            InvalidDeleteException: If the file is invalid after deleting the step.
        """
        self._make_change(self._delete_step, step_index)

    def add_step(
        self,
        previous_step_index: int,
        step_text: str,
    ) -> None:
        """Adds a step to the file. This function will change the original file.
        If an exception is thrown the file will not be changed.

        Args:
            previous_step_index (int): The index of the previous step of the new step.
            step_text (str): The text of the step to add.

        Raises:
            InvalidFileException: If the file being changed is not valid.
            InvalidAddException: If the file is invalid after adding the step.
        """
        self._make_change(self._add_step, previous_step_index, step_text)

    def change_steps(self, changes: List[CoqChange]):
        """Changes the steps of the original Coq file transactionally.
        If an exception is thrown the file will not be changed.

        Args:
            changes (List[CoqChange]): The changes to be applied to the Coq file.

        Raises:
            InvalidFileException: If the file being changed is not valid.
            InvalidChangeException: If the file is invalid after applying the changes.
            NotImplementedError: If the changes contain a CoqChange that is not a CoqAdd or CoqDelete.
        """
        self._make_change(self.__change_steps, changes)

    def save_vo(self):
        """Compiles the vo file for this Coq file."""
        uri = f"file://{self._path}"
        try:
            self.coq_lsp_client.save_vo(TextDocumentIdentifier(uri))
        except Exception as e:
            self._handle_exception(e)
            raise e

    def close(self):
        """Closes all resources used by this object."""
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self._path)
