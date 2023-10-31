import os
import shutil
import uuid
import tempfile
import subprocess
from coqpyt.lsp.structs import (
    TextDocumentItem,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
)
from coqpyt.lsp.structs import ResponseError, ErrorCodes, Diagnostic
from coqpyt.coq.lsp.structs import Position, GoalAnswer, RangedSpan
from coqpyt.coq.structs import Step, FileContext, Term, TermType, SegmentType
from coqpyt.coq.lsp.client import CoqLspClient
from coqpyt.coq.exceptions import *
from coqpyt.coq.changes import *
from typing import List, Optional
from packaging import version


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
        self.__init_coq_version(coqtop)
        self.curr_module: List[str] = []
        self.curr_module_type: List[str] = []
        self.curr_section: List[str] = []
        self.__segment_stack: List[SegmentType] = []
        self.context = FileContext()
        self.__anonymous_id: Optional[int] = None
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

    def __init_coq_version(self, coqtop):
        output = subprocess.check_output(f"{coqtop} -v", shell=True)
        coq_version = output.decode("utf-8").split("\n")[0].split()[-1]
        outdated = version.parse(coq_version) < version.parse("8.18")

        # For version 8.18, we ignore the tags [VernacSynterp] and [VernacSynPure]
        # and use the "ntn_decl" prefix when handling where notations
        # For older versions, we only tested 8.17, so we provide no claims about
        # versions prior to that.

        self.__expr = lambda e: e if outdated else e[1]
        self.__where_notation_key = "decl_ntn" if outdated else "ntn_decl"

    @property
    def curr_step(self):
        return self.steps[self.steps_taken]

    @property
    def prev_step(self):
        return self.steps[self.steps_taken - 1]

    @staticmethod
    def get_id(id: List) -> str:
        if id[0] == "Ser_Qualid":
            return ".".join([l[1] for l in reversed(id[1][1])] + [id[2][1]])
        elif id[0] == "Id":
            return id[1]
        return None

    @staticmethod
    def get_ident(el: List) -> Optional[str]:
        if (
            len(el) == 3
            and el[0] == "GenArg"
            and el[1][0] == "Rawwit"
            and el[1][1][0] == "ExtraArg"
        ):
            if el[1][1][1] == "identref":
                return el[2][0][1][1]
            elif el[1][1][1] == "ident":
                return el[2][1]
        return None

    @staticmethod
    def get_v(el):
        if isinstance(el, dict) and "v" in el:
            return el["v"]
        elif isinstance(el, list) and len(el) == 2 and el[0] == "v":
            return el[1]
        return None

    def expr(self, step: RangedSpan) -> Optional[List]:
        if (
            step.span is not None
            and isinstance(step.span, dict)
            and "v" in step.span
            and isinstance(step.span["v"], dict)
            and "expr" in step.span["v"]
        ):
            return self.__expr(step.span["v"]["expr"])

        return [None]

    def __short_text(
        self, text: str, curr_step: RangedSpan, prev_step: Optional[RangedSpan] = None
    ):
        curr_range = curr_step.range
        nlines = curr_range.end.line - curr_range.start.line + 1
        lines = text.split("\n")[-nlines:]

        prev_range = None if prev_step is None else prev_step.range
        if prev_range is None or prev_range.end.line < curr_range.start.line:
            start = curr_range.start.character
        else:
            start = curr_range.start.character - prev_range.end.character

        lines[-1] = lines[-1][: curr_range.end.character]
        lines[0] = lines[0][start:]

        return " ".join(" ".join(lines).split())

    def __add_term(self, name: str, step: Step, term_type: TermType):
        term = Term(step, term_type, self.path, self.curr_module[:])
        if term.type == TermType.NOTATION:
            self.context.update(terms={name: term})
            return

        full_name = lambda name: ".".join(self.curr_module + [name])
        self.context.update(terms={full_name(name): term})

        curr_file_module = ""
        for module in reversed(self.file_module):
            curr_file_module = module + "." + curr_file_module
            self.context.update(terms={curr_file_module + name: term})

    @staticmethod
    def __get_term_type(expr: List) -> TermType:
        if expr[0] == "VernacStartTheoremProof":
            return getattr(TermType, expr[1][0].upper())
        elif expr[0] == "VernacDefinition":
            return TermType.DEFINITION
        elif expr[0] in ["VernacNotation", "VernacSyntacticDefinition"]:
            return TermType.NOTATION
        elif expr[0] == "VernacExtend" and expr[1][0] == "Obligations":
            return TermType.OBLIGATION
        elif expr[0] == "VernacInductive" and expr[1][0] == "Class":
            return TermType.CLASS
        elif expr[0] == "VernacInductive" and expr[1][0] in ["Record", "Structure"]:
            return TermType.RECORD
        elif expr[0] == "VernacInductive" and expr[1][0] == "Variant":
            return TermType.VARIANT
        elif expr[0] == "VernacInductive" and expr[1][0] == "CoInductive":
            return TermType.COINDUCTIVE
        elif expr[0] == "VernacInductive":
            return TermType.INDUCTIVE
        elif expr[0] == "VernacInstance":
            return TermType.INSTANCE
        elif expr[0] == "VernacCoFixpoint":
            return TermType.COFIXPOINT
        elif expr[0] == "VernacFixpoint":
            return TermType.FIXPOINT
        elif expr[0] == "VernacScheme":
            return TermType.SCHEME
        elif expr[0] == "VernacExtend" and expr[1][0].startswith("Derive"):
            return TermType.DERIVE
        elif expr[0] == "VernacExtend" and expr[1][0].startswith("AddSetoid"):
            return TermType.SETOID
        elif expr[0] == "VernacExtend" and expr[1][0].startswith(
            ("AddRelation", "AddParametricRelation")
        ):
            return TermType.RELATION
        elif (
            expr[0] == "VernacExtend" and expr[1][0] == "VernacDeclareTacticDefinition"
        ):
            return TermType.TACTIC
        elif expr[0] == "VernacExtend" and expr[1][0] == "Function":
            return TermType.FUNCTION
        else:
            return TermType.OTHER

    # Simultaneous definition of terms and notations (where clause)
    # https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#simultaneous-definition-of-terms-and-notations
    def __handle_where_notations(self, expr: List, term_type: TermType):
        spans = []
        if (
            term_type
            in [
                TermType.VARIANT,
                TermType.INDUCTIVE,
            ]
            and len(expr) > 2
            and isinstance(expr[2], list)
            and len(expr[2]) > 0
            and isinstance(expr[2][0], list)
            and len(expr[2][0]) > 1
            and isinstance(expr[2][0][1], list)
            and len(expr[2][0][1]) > 0
        ):
            spans = expr[2][0][1]
        elif (
            term_type == TermType.FIXPOINT
            and len(expr) > 2
            and isinstance(expr[2], list)
            and len(expr[2]) > 0
            and isinstance(expr[2][0], dict)
            and "notations" in expr[2][0]
            and isinstance(expr[2][0]["notations"], list)
            and len(expr[2][0]["notations"]) > 0
        ):
            spans = expr[2][0]["notations"]

        # handles when multiple notations are defined
        for span in spans:
            name = FileContext.get_notation_key(
                span[f"{self.__where_notation_key}_string"]["v"],
                span[f"{self.__where_notation_key}_scope"],
            )
            self.__add_term(name, self.curr_step, TermType.NOTATION)

    def __process_step(self, sign):
        def traverse_expr(expr):
            inductive = expr[0] == "VernacInductive"
            extend = expr[0] == "VernacExtend"
            stack, res = expr[:0:-1], []
            while len(stack) > 0:
                el = stack.pop()
                v = CoqFile.get_v(el)
                if v is not None and isinstance(v, list) and len(v) == 2:
                    id = CoqFile.get_id(v)
                    if id is not None:
                        if not inductive:
                            return [id]
                        res.append(id)
                    elif v[0] == "Name":
                        if not inductive:
                            return [v[1][1]]
                        res.append(v[1][1])

                elif isinstance(el, dict):
                    for v in reversed(el.values()):
                        if isinstance(v, (dict, list)):
                            stack.append(v)
                elif isinstance(el, list):
                    if len(el) > 0 and el[0] == "CLocalAssum":
                        continue

                    ident = CoqFile.get_ident(el)
                    if ident is not None and extend:
                        return [ident]

                    for v in reversed(el):
                        if isinstance(v, (dict, list)):
                            stack.append(v)
            return res

        try:
            # TODO: A negative sign should handle things differently. For example:
            #   - names should be removed from the context
            #   - curr_module should change as you leave or re-enter modules

            text = self.curr_step.short_text

            # FIXME Let (and maybe Variable) should be handled. However,
            # I think we can't handle them as normal Locals since they are
            # specific to a section.
            for keyword in [
                "Variable",
                "Let",
                "Context",
                "Hypothesis",
                "Hypotheses",
            ]:
                if text.startswith(keyword):
                    return
            expr = self.expr(self.curr_step.ast)
            if expr == [None]:
                return
            if expr[0] == "VernacExtend" and expr[1][0] == "VernacSolve":
                return
            term_type = CoqFile.__get_term_type(expr)

            if expr[0] == "VernacEndSegment":
                if len(self.__segment_stack) == 0:
                    return
                match self.__segment_stack.pop():
                    case SegmentType.MODULE:
                        self.curr_module.pop()
                    case SegmentType.MODULE_TYPE:
                        self.curr_module_type.pop()
                    case SegmentType.SECTION:
                        self.curr_section.pop()
            elif expr[0] == "VernacDefineModule":
                self.curr_module.append(expr[2]["v"][1])
                self.__segment_stack.append(SegmentType.MODULE)
            elif expr[0] == "VernacDeclareModuleType":
                self.curr_module_type.append(expr[1]["v"][1])
                self.__segment_stack.append(SegmentType.MODULE_TYPE)
            elif expr[0] == "VernacBeginSection":
                self.curr_section.append(expr[1]["v"][1])
                self.__segment_stack.append(SegmentType.SECTION)

            # HACK: We ignore terms inside a Module Type since they can't be used outside
            # and should be overriden.
            elif len(self.curr_module_type) > 0:
                return
            elif expr[0] == "VernacExtend" and expr[1][0] == "VernacTacticNotation":
                # FIXME: Handle this case
                return
            elif expr[0] == "VernacNotation":
                name = text.split('"')[1].strip()
                if text[:-1].split(":")[-1].endswith("_scope"):
                    name += " : " + text[:-1].split(":")[-1].strip()
                self.__add_term(name, self.curr_step, TermType.NOTATION)
            elif expr[0] == "VernacSyntacticDefinition":
                name = text.split(" ")[1]
                if text[:-1].split(":")[-1].endswith("_scope"):
                    name += " : " + text[:-1].split(":")[-1].strip()
                self.__add_term(name, self.curr_step, TermType.NOTATION)
            elif expr[0] == "VernacInstance" and expr[1][0]["v"][0] == "Anonymous":
                # FIXME: The name should be "<Class>_instance_N"
                self.__add_term("_anonymous", self.curr_step, term_type)
            elif expr[0] == "VernacDefinition" and expr[2][0]["v"][0] == "Anonymous":
                # We associate the anonymous term to the same name used internally by Coq
                if self.__anonymous_id is None:
                    name, self.__anonymous_id = "Unnamed_thm", 0
                else:
                    name = f"Unnamed_thm{self.__anonymous_id}"
                    self.__anonymous_id += 1
                self.__add_term(name, self.curr_step, term_type)
            elif term_type == TermType.DERIVE:
                name = CoqFile.get_ident(expr[2][0])
                self.__add_term(name, self.curr_step, term_type)
                if expr[1][0] == "Derive":
                    prop = CoqFile.get_ident(expr[2][2])
                    self.__add_term(prop, self.curr_step, term_type)
            else:
                names = traverse_expr(expr)
                for name in names:
                    self.__add_term(name, self.curr_step, term_type)

            self.__handle_where_notations(expr, term_type)
        finally:
            self.steps_taken += sign

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

    def __in_proof(self, goals: Optional[GoalAnswer]):
        def empty_stack(stack):
            # e.g. [([], [])]
            for tuple in stack:
                if len(tuple[0]) > 0 or len(tuple[1]) > 0:
                    return False
            return True

        goals = goals.goals
        return goals is not None and (
            len(goals.goals) > 0
            or not empty_stack(goals.stack)
            or len(goals.shelf) > 0
            or goals.bullet is not None
        )

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

    def _delete_step(
        self,
        step_index: int,
        in_proof: bool = False,
        validate_file: bool = True,
    ) -> None:
        if not in_proof and not self.__in_proof(
            self._goals(self.steps[step_index - 1].ast.range.end)
        ):
            raise NotImplementedError(
                "Deleting steps outside of a proof is not implemented yet"
            )

        with open(self.__path, "r") as f:
            lines = f.readlines()

        with open(self.path, "w") as f:
            step = self.steps[step_index]
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
            text = "".join(lines)
            f.write(text)

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

        previous_steps.pop(step_index)
        for i, step in enumerate(previous_steps):
            step.text, step.ast = self.steps[i].text, self.steps[i].ast
            step.diagnostics = self.steps[i].diagnostics
        self.steps = previous_steps

    def _add_step(
        self,
        step_text: str,
        previous_step_index: int,
        in_proof: bool = False,
        validate_file: bool = True,
    ) -> None:
        if validate_file and not self.is_valid:
            raise InvalidFileException(self.path)

        if not in_proof and not self.__in_proof(
            self._goals(self.steps[previous_step_index].ast.range.end)
        ):
            raise NotImplementedError(
                "Deleting steps outside of a proof is not implemented yet"
            )

        with open(self.__path, "r") as f:
            lines = f.read().split("\n")

        with open(self.path, "w") as f:
            previous_step = self.steps[previous_step_index]
            end_line = previous_step.ast.range.end.line
            end_char = previous_step.ast.range.end.character
            lines[end_line] = (
                lines[end_line][:end_char] + step_text + lines[end_line][end_char + 1 :]
            )
            text = "\n".join(lines)
            f.write(text)

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

    def _change_steps(self, changes: List[CoqChange]):
        offset_steps = 0
        previous_steps_size = len(self.steps)

        for i, change in enumerate(changes):
            if isinstance(change, CoqAddStep):
                self._add_step(
                    change.step_text,
                    change.previous_step_index,
                    validate_file=False,
                )
                offset_steps += 1
            elif isinstance(change, CoqDeleteStep):
                self._delete_step(change.step_index, validate_file=False)
                offset_steps -= 1
            else:
                raise NotImplementedError(f"Unknown change: {change}")

        if len(self.steps) != previous_steps_size + offset_steps or not self.is_valid:
            raise InvalidChangeException()

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
    def in_proof(self) -> bool:
        """
        Returns:
            bool: True if the current step is inside a proof
        """
        return self.__in_proof(self.current_goals())

    @property
    def terms(self) -> List[Term]:
        """
        Returns:
            List[Term]: The terms of the file already executed
        """
        return list(
            filter(
                lambda term: term.file_path == self.path, self.context.terms.values()
            )
        )

    @property
    def diagnostics(self) -> List[Diagnostic]:
        """
        Returns:
            List[Diagnostic]: The diagnostics of the file.
                Includes all messages given by Coq.
        """
        uri = f"file://{self.__path}"
        return self.coq_lsp_client.lsp_endpoint.diagnostics[uri]

    def get_term_type(self, ast: RangedSpan) -> TermType:
        expr = self.expr(ast)
        if expr is not None:
            return CoqFile.__get_term_type(expr)
        return TermType.OTHER

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

        # FIXME: for now we ignore the terms in the context when going backwards
        # on the file
        if sign == 1:
            for _ in range(nsteps):
                self.__process_step(sign)
            return self.steps[initial_steps_taken : self.steps_taken]
        else:
            for _ in range(nsteps):
                self.steps_taken -= 1
                if not self.in_proof:
                    self.steps_taken = initial_steps_taken
                    raise NotImplementedError(
                        "Going backwards outside of a proof is not implemented yet"
                    )
            return self.steps[self.steps_taken - 1 : initial_steps_taken]

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
        step_text: str,
        previous_step_index: int,
    ) -> None:
        """Adds a step to the file. The step must be inside a proof.
        This function will change the original file. If an exception is thrown
        the file will not be changed.

        Args:
            step_text (str): The text of the step to add.
            previous_step_index (int): The index of the previous step of the new step.

        Raises:
            NotImplementedError: If the step added is not on a proof.
            InvalidFileException: If the file being changed is not valid.
            InvalidStepException: If the step added is not valid
        """
        self._make_change(self._add_step, step_text, previous_step_index)

    def change_steps(self, changes: List[CoqChange]):
        """Changes the steps of the Coq file transactionally.

        Args:
            changes (List[CoqChange]): The changes to be applied to the Coq file.
        """
        self._make_change(self._change_steps, changes)

    def run(self) -> List[Step]:
        """Executes all the steps in the file.

        Returns:
            List[Step]: List of all the steps in the file.
        """
        return self.exec(len(self.steps))

    def current_goals(self) -> Optional[GoalAnswer]:
        """Get goals in current position.

        Returns:
            Optional[GoalAnswer]: Goals in the current position if there are goals
        """
        end_pos = (
            Position(0, 0) if self.steps_taken == 0 else self.prev_step.ast.range.end
        )

        if end_pos != self.__last_end_pos:
            self.__current_goals = self._goals(end_pos)
            self.__last_end_pos = end_pos

        return self.__current_goals

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
