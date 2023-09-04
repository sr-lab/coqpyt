import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.lsp_structs import ResponseError, ErrorCodes
from coqlspclient.coq_lsp_structs import Position, GoalAnswer, RangedSpan, Range
from coqlspclient.coq_structs import Step, FileContext, Term, TermType, SegmentType
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

    def __init__(
        self,
        file_path: str,
        library: Optional[str] = None,
        timeout: int = 2,
        workspace: Optional[str] = None,
    ):
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
            uri = f"file://{self.__path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)
        uri = f"file://{self.__path}"
        with open(self.__path, "r") as f:
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
        self.curr_module_type: List[str] = []
        self.curr_section: List[str] = []
        self.__segment_stack: List[SegmentType] = []
        self.context = FileContext()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path, library):
        self.file_module = [] if library is None else library.split(".")
        self.__from_lib = self.file_module[:1] == ["Coq"]
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
        if not (isinstance(e, ResponseError) and e.code == ErrorCodes.ServerQuit.value):
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        if self.__from_lib:
            os.remove(self.__path)

    def __validate(self):
        uri = f"file://{self.__path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            self.is_valid = True
            return

        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            if diagnostic.severity == 1:
                self.is_valid = False
                return
        self.is_valid = True

    @staticmethod
    def expr(step: RangedSpan) -> Optional[List]:
        if (
            step.span is not None
            and isinstance(step.span, dict)
            and "v" in step.span
            and isinstance(step.span["v"], dict)
            and "expr" in step.span["v"]
        ):
            return step.span["v"]["expr"]

        return [None]

    def __step_expr(self):
        curr_step = self.ast[self.steps_taken]
        return CoqFile.expr(curr_step)

    def __get_text(self, range: Range, trim: bool = False):
        end_line = range.end.line
        end_character = range.end.character

        if trim:
            start_line = range.start.line
            start_character = range.start.character
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

    def __step_text(self, trim=False):
        curr_step = self.ast[self.steps_taken]
        return self.__get_text(curr_step.range, trim=trim)

    def __add_term(self, name: str, ast: RangedSpan, text: str, term_type: TermType):
        term = Term(text, ast, term_type, self.path, self.curr_module[:])
        if term.type == TermType.NOTATION:
            self.context.update(terms={name: term})
            return

        full_name = lambda name: ".".join(self.curr_module + [name])
        self.context.update(terms={full_name(name): term})

        curr_file_module = ""
        for module in self.file_module[::-1]:
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
        elif expr[0] == "VernacInductive":
            return TermType.INDUCTIVE
        elif expr[0] == "VernacInstance":
            return TermType.INSTANCE
        elif expr[0] == "VernacFixpoint":
            return TermType.FIXPOINT
        elif expr[0] == "VernacScheme":
            return TermType.SCHEME
        elif (
            len(expr) > 1
            and isinstance(expr[1], list)
            and expr[1][0] == "VernacDeclareTacticDefinition"
        ):
            return TermType.TACTIC
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
            range = Range(
                Position(
                    span["decl_ntn_string"]["loc"]["line_nb"] - 1,
                    span["decl_ntn_string"]["loc"]["bp"]
                    - span["decl_ntn_string"]["loc"]["bol_pos"],
                ),
                Position(
                    span["decl_ntn_interp"]["loc"]["line_nb_last"] - 1,
                    span["decl_ntn_interp"]["loc"]["ep"]
                    - span["decl_ntn_interp"]["loc"]["bol_pos"],
                ),
            )
            text = self.__get_text(range, trim=True)
            name = FileContext.get_notation_key(
                span["decl_ntn_string"]["v"], span["decl_ntn_scope"]
            )
            if span["decl_ntn_scope"] is not None:
                text += " : " + span["decl_ntn_scope"]
            text = "Notation " + text
            self.__add_term(name, RangedSpan(range, span), text, TermType.NOTATION)

    def __get_tactic_name(self, expr):
        if len(expr[2][0][2][0][1][0]) == 2 and expr[2][0][2][0][1][0][0] == "v":
            id, name = expr[2][0][2][0][1][0][1], ""
            if id[0] == "Ser_Qualid" and id[1][0] == "DirPath" and id[2][0] == "Id":
                for dir_el in id[1][1]:
                    name += dir_el[1] + "."
                name += id[2][1]
            elif id[0] == "Id":
                name = id[1]

            if name != "":
                return name

            return None

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
                        return [res[0]]
                return res

            return []

        try:
            # TODO: A negative sign should handle things differently. For example:
            #   - names should be removed from the context
            #   - curr_module should change as you leave or re-enter modules
            text = self.__step_text(trim=True)
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
            expr = self.__step_expr()
            if expr == [None]:
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
            elif (
                len(expr) >= 2
                and isinstance(expr[1], list)
                and len(expr[1]) == 2
                and expr[1][0] == "VernacDeclareTacticDefinition"
            ):
                name = self.__get_tactic_name(expr)
                self.__add_term(name, self.ast[self.steps_taken], text, TermType.TACTIC)
            elif expr[0] == "VernacNotation":
                name = text.split('"')[1]
                if text[:-1].split(":")[-1].endswith("_scope"):
                    name += " : " + text[:-1].split(":")[-1].strip()
                self.__add_term(
                    name, self.ast[self.steps_taken], text, TermType.NOTATION
                )
            elif expr[0] == "VernacSyntacticDefinition":
                name = text.split(" ")[1]
                if text[:-1].split(":")[-1].endswith("_scope"):
                    name += " : " + text[:-1].split(":")[-1].strip()
                self.__add_term(
                    name, self.ast[self.steps_taken], text, TermType.NOTATION
                )
            else:
                names = traverse_ast(expr)
                for name in names:
                    self.__add_term(name, self.ast[self.steps_taken], text, term_type)

            self.__handle_where_notations(expr, term_type)
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

        def empty_stack(stack):
            # e.g. [([], [])]
            for tuple in stack:
                if len(tuple[0]) > 0 or len(tuple[1]) > 0:
                    return False
            return True

        goals = self.current_goals().goals
        return goals is not None and (
            len(goals.goals) > 0
            or not empty_stack(goals.stack)
            or len(goals.shelf) > 0
            or goals.bullet is not None
        )

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

    @staticmethod
    def get_term_type(ast: RangedSpan) -> TermType:
        expr = CoqFile.expr(ast)
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
        uri = f"file://{self.__path}"
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
