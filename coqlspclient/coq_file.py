import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.lsp_structs import ResponseError, ErrorCodes
from coqlspclient.coq_lsp_structs import Step, Position, FileContext
from coqlspclient.coq_lsp_client import CoqLspClient
from typing import List


class CoqFile(object):
    def __init__(self, file_path: str, timeout: int = 2):
        self.__init_path(file_path)
        uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)
        with open(self.path, "r") as f:
            self.lines = f.read().split("\n")

        try:
            self.coq_lsp_client.didOpen(
                TextDocumentItem(uri, "coq", 1, "\n".join(self.lines))
            )
            self.ast = self.coq_lsp_client.get_document(
                TextDocumentIdentifier(uri)
            ).spans
        except Exception as e:
            self.__handle_exception(e)
            raise e

        self.__validate()
        self.steps_taken: int = 0
        self.__init_file_module(file_path)
        self.curr_module: List[str] = []
        self.context = FileContext()

    def __init_path(self, file_path):
        self.from_lib = os.path.join("lib", "coq") in file_path
        if not self.from_lib:
            self.path = file_path
            return
        
        # Coq LSP cannot open files from Coq.Init, so we need to work with a copy of such files.
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "coq_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)
        self.path = new_path

    def __init_file_module(self, file_path):
        self.file_module = []
        if self.from_lib:
            self.file_module.append("Coq")
        self.file_module.extend(
            filter(lambda f: len(f) > 0 and f[0].isupper(), file_path.split(os.sep))
        )
        # File
        if len(self.file_module) > 0 and self.file_module[-1].endswith(".v"):
            self.file_module[-1] = self.file_module[-1][:-2]

    def __handle_exception(self, e):
        if not (
            isinstance(e, ResponseError)
            and e.code == ErrorCodes.ServerQuit.value
        ):
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        if self.from_lib:
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
            prev_step = None if self.steps_taken == 0 else self.ast[self.steps_taken - 1]
            start_line = 0 if prev_step is None else prev_step.range.end.line
            start_character = 0 if prev_step is None else prev_step.range.end.character

        lines = self.lines[start_line : end_line + 1]
        lines[-1] = lines[-1][: end_character + 1]
        lines[0] = lines[0][start_character:]
        text = "\n".join(lines)
        return " ".join(text.split()) if trim else text
    
    def __add_alias(self, name):
        curr_file_module = ""
        for module in self.file_module[::-1]:
            curr_file_module = module + "." + curr_file_module
            self.context.update(aliases={curr_file_module + name: name})

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
            for keyword in ["Local", "Variable", "Let", "Context", "Hypothesis", "Hypotheses"]:
                if text.startswith(keyword):
                    return
            expr = self.__step_expr()
            if expr == [None]:
                return

            full_name = lambda name: ".".join(self.curr_module + [name])
            if (
                len(expr) >= 2
                and isinstance(expr[1], list)
                and len(expr[1]) == 2
                and expr[1][0] == "VernacDeclareTacticDefinition"
            ):
                name = expr[2][0][2][0][1][0][1][1]
                self.context.update(terms={full_name(name): text})
                self.__add_alias(name)
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
                    self.context.update(terms={full_name(name): text})
                    self.__add_alias(name)
        finally:
            self.steps_taken += sign
        
    def exec(self, nsteps=1):
        steps = []
        sign = 1 if nsteps > 0 else -1
        nsteps = min(nsteps * sign, len(self.ast) - self.steps_taken if sign > 0 else self.steps_taken)
        for _ in range(nsteps):
            steps.append(Step(self.__step_text(), self.ast[self.steps_taken]))
            self.__process_step(sign)
        return steps

    def run(self):
        return self.exec(len(self.ast))
    
    def checked(self):
        return self.steps_taken == len(self.ast)
    
    def current_goals(self):
        uri = f"file://{self.path}"
        end_pos = Position(0, 0) if self.steps_taken == 0 else self.ast[self.steps_taken - 1].range.end
        try:
            return self.coq_lsp_client.proof_goals(TextDocumentIdentifier(uri), end_pos)
        except Exception as e:
            self.__handle_exception(e)
            raise e

    def in_proof(self):
        return self.current_goals().goals is not None

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        if self.from_lib:
            os.remove(self.path)