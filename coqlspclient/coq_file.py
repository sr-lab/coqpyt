import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.lsp_structs import ResponseError, ErrorCodes
from coqlspclient.coq_lsp_structs import Step, Position, FileContext, GoalAnswer
from coqlspclient.coq_lsp_client import CoqLspClient
from typing import List, Optional


class CoqFile(object):
    """Abstraction to interact with a Coq file

    Attributes:
        coq_lsp_client (CoqLspClient): coq-lsp client used on the file
        ast (List[RangedSpan]): AST of the Coq file. Each element is a step
            of execution in the Coq file.
        steps_taken (int): The number of steps already executed
        curr_module (List[str]): A list correspondent to the module path in the
            current step. For instance, if the current module is `Ex.Test`, the
            list will be ['Ex', 'Test'].
        context (FileContext): The context defined in the file.
        path (str): Path of the file. If the file is from the Coq library, a
            temporary file will be used.
        file_module(List[str]): Module where the file is included.
    """

    def __init__(self, file_path: str, library: Optional[str] = None, timeout: int = 2, workspace: Optional[str] = None):
        """Creates a CoqFile.

        Args:
            file_path (str): Absolute path of the Coq file.
            library (Optional[str], optional): The library of the file. Defaults to None.
            timeout (int, optional): Timeout used in coq-lsp. Defaults to 2.
            workspace(Optional[str], optional): Absolute path for the workspace.
                If the workspace is not defined, the workspace is equal to the 
                path of the file.
        """
        self.__init_path(file_path, library)
        if workspace is not None:
            uri = f"file://{workspace}"
        else:
            uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)
        uri = f"file://{self.path}"
        with open(self.path, "r") as f:
            self.__lines = f.read().split("\n")

        try:
            self.coq_lsp_client.didOpen(
                TextDocumentItem(uri, "coq", 1, "\n".join(self.__lines))
            )
            self.ast = self.coq_lsp_client.get_document(
                TextDocumentIdentifier(uri)
            ).spans
        except Exception as e:
            self.__handle_exception(e)
            raise e

        self.__validate()
        self.steps_taken: int = 0
        self.curr_module: List[str] = []
        self.context = FileContext()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path, library):
        self.file_module = [] if library is None else library.split(".")
        self.__from_lib = self.file_module[:1] == ["Coq"]
        if not self.__from_lib:
            self.path = file_path
            return

        # Coq LSP cannot open files from Coq library, so we need to work with
        # a copy of such files.
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "coq_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)
        self.path = new_path

    def __handle_exception(self, e):
        if not (isinstance(e, ResponseError) and e.code == ErrorCodes.ServerQuit.value):
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self.path)

    def __validate(self):
        uri = f"file://{self.path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            self.is_valid = True
            return

        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            if diagnostic.severity == 1:
                self.is_valid = False
                return
        self.is_valid = True

    def __step_expr(self):
        curr_step = self.ast[self.steps_taken]
        if (
            curr_step.span is not None
            and isinstance(curr_step.span, dict)
            and "v" in curr_step.span
            and isinstance(curr_step.span["v"], dict)
            and "expr" in curr_step.span["v"]
        ):
            return curr_step.span["v"]["expr"]
        return [None]

    def __step_text(self, trim=False):
        curr_step = self.ast[self.steps_taken]
        end_line = curr_step.range.end.line
        end_character = curr_step.range.end.character

        if trim:
            start_line = curr_step.range.start.line
            start_character = curr_step.range.start.character
        else:
            prev_step = (
                None if self.steps_taken == 0 else self.ast[self.steps_taken - 1]
            )
            start_line = 0 if prev_step is None else prev_step.range.end.line
            start_character = 0 if prev_step is None else prev_step.range.end.character

        lines = self.__lines[start_line : end_line + 1]
        lines[-1] = lines[-1][: end_character + 1]
        lines[0] = lines[0][start_character:]
        text = "\n".join(lines)
        return " ".join(text.split()) if trim else text

    def __add_term(self, name: str, text: str):
        full_name = lambda name: ".".join(self.curr_module + [name])
        self.context.update(terms={full_name(name): text})

        curr_file_module = ""
        for module in self.file_module[::-1]:
            curr_file_module = module + "." + curr_file_module
            self.context.update(terms={curr_file_module + name: text})

    def __process_step(self, sign):
        def traverse_ast(el, inductive=False):
            if isinstance(el, dict):
                if "v" in el and isinstance(el["v"], list) and len(el["v"]) == 2:
                    if el["v"][0] == "Id":
                        return [el["v"][1]]
                    if el["v"][0] == "Name":
                        return [el["v"][1][1]]

                return [x for v in el.values() for x in traverse_ast(v, inductive)]
            elif isinstance(el, list):
                if len(el) > 0:
                    if el[0] == "CLocalAssum":
                        return []
                    if el[0] == "VernacInductive":
                        inductive = True

                res = []
                for v in el:
                    res.extend(traverse_ast(v, inductive))
                    if not inductive and len(res) > 0:
                        return res
                return res

            return []

        try:
            # TODO: A negative sign should handle things differently. For example:
            #   - names should be removed from the context
            #   - curr_module should change as you leave or re-enter modules
            text = self.__step_text(trim=True)
            for keyword in [
                "Variable",
                "Let",
                "Context",
                "Hypothesis",
                "Hypotheses",
            ]:
                if text.startswith(keyword):
                    return
            expr = self.__step_expr()
            if expr == [None]:
                return

            if (
                len(expr) >= 2
                and isinstance(expr[1], list)
                and len(expr[1]) == 2
                and expr[1][0] == "VernacDeclareTacticDefinition"
            ):
                name = expr[2][0][2][0][1][0][1][1]
                self.__add_term(name, text)
            elif expr[0] == "VernacNotation":
                self.context.update(notations=[text])
            elif expr[0] == "VernacDefineModule":
                self.curr_module.append(expr[2]["v"][1])
            elif expr[0] == "VernacEndSegment":
                if [expr[1]["v"][1]] == self.curr_module[-1:]:
                    self.curr_module.pop()
            elif expr[0] != "VernacBeginSection":
                names = traverse_ast(expr)
                for name in names:
                    self.__add_term(name, text)
        finally:
            self.steps_taken += sign

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
        return self.steps_taken == len(self.ast)

    @property
    def in_proof(self) -> bool:
        """
        Returns:
            bool: True if the current step is inside a proof
        """
        return self.current_goals().goals is not None

    def exec(self, nsteps=1) -> List[Step]:
        """Execute steps in the file.

        Args:
            nsteps (int, optional): Number of steps to execute. Defaults to 1.

        Returns:
            List[Step]: List of steps executed.
        """
        steps: List[Step] = []
        sign = 1 if nsteps > 0 else -1
        nsteps = min(
            nsteps * sign,
            len(self.ast) - self.steps_taken if sign > 0 else self.steps_taken,
        )
        for _ in range(nsteps):
            steps.append(Step(self.__step_text(), self.ast[self.steps_taken]))
            self.__process_step(sign)
        return steps

    def run(self) -> List[Step]:
        """Executes all the steps in the file.

        Returns:
            List[Step]: List of all the steps in the file.
        """
        return self.exec(len(self.ast))

    def current_goals(self) -> Optional[GoalAnswer]:
        """Get goals in current position.

        Returns:
            Optional[GoalAnswer]: Goals in the current position if there are goals
        """
        uri = f"file://{self.path}"
        end_pos = (
            Position(0, 0)
            if self.steps_taken == 0
            else self.ast[self.steps_taken - 1].range.end
        )
        try:
            return self.coq_lsp_client.proof_goals(TextDocumentIdentifier(uri), end_pos)
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def save_vo(self):
        """Compiles the vo file for this Coq file."""
        uri = f"file://{self.path}"
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
            os.remove(self.path)
