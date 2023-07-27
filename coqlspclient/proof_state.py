import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import (
    TextDocumentItem,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
)
from pylspclient.lsp_structs import (
    TextDocumentContentChangeEvent,
    Position,
    ResponseError,
    ErrorCodes,
)
from coqlspclient.coq_lsp_structs import Step, Result, Query
from coqlspclient.coq_lsp_client import CoqLspClient


class ProofState(object):
    def __init__(self, file_path, timeout=2):
        file_uri = f"file://{file_path}"
        self.coq_lsp_client = CoqLspClient(file_uri, timeout=timeout)
        try:
            with open(file_path, "r") as f:
                self.lines = f.read().split("\n")
                self.coq_lsp_client.didOpen(
                    TextDocumentItem(file_uri, "coq", 1, "\n".join(self.lines))
                )
            self.path = file_path
            self.ast = self.coq_lsp_client.get_document(
                TextDocumentIdentifier(file_uri)
            )
            self.ast = self.ast["spans"]
            self.current_step = None
            self.in_proof = False
            self.terms = {}
            self.alias_terms = {}
            self.notations = []
            self.__init_aux_file()
        except Exception as e:
            if (
                not isinstance(e, ResponseError)
                or e.code != ErrorCodes.ServerQuit.value
            ):
                self.coq_lsp_client.shutdown()
                self.coq_lsp_client.exit()
            raise e

    def __init_aux_file(self):
        dir = os.path.dirname(self.path)
        new_base_name = os.path.basename(self.path).split(".")
        new_base_name = (
            new_base_name[0]
            + f"new{str(uuid.uuid4()).replace('-', '')}."
            + new_base_name[1]
        )
        self.aux_path = os.path.join(dir, new_base_name)
        self.aux_file_text = ""
        self.aux_file_version = 1
        with open(self.aux_path, "w"):
            # Create empty file
            pass

    def __get_expr(self, ast_step):
        if (
            isinstance(ast_step, dict)
            and "span" in ast_step
            and isinstance(ast_step["span"], dict)
            and "v" in ast_step["span"]
            and isinstance(ast_step["span"]["v"], dict)
            and "expr" in ast_step["span"]["v"]
        ):
            return ast_step["span"]["v"]["expr"]
        return [None]

    def __get_theorem_name(self, expr):
        return expr[2][0][0][0]["v"][1]

    def __write_on_aux_file(self, text):
        self.aux_file_text += text
        with open(self.aux_path, "a") as f:
            f.write(text)

    def __call_didOpen(self):
        uri = f"file://{self.aux_path}"
        self.coq_lsp_client.didOpen(TextDocumentItem(uri, "coq", 1, self.aux_file_text))

    def __call_didChange(self):
        self.aux_file_version += 1
        uri = f"file://{self.aux_path}"
        self.coq_lsp_client.didChange(
            VersionedTextDocumentIdentifier(uri, self.aux_file_version),
            [TextDocumentContentChangeEvent(None, None, self.aux_file_text)],
        )

    def __command(self, keywords, search):
        for keyword in keywords:
            command = f"\n{keyword} {search}."
            self.__write_on_aux_file(command)

    def __get_diagnostics(self, coq_lsp_client, file_path, keywords, search, line):
        res = []
        uri = f"file://{file_path}"

        for keyword in keywords:
            kw_res = None
            queries = self.get_queries(
                coq_lsp_client, TextDocumentIdentifier(uri), keyword
            )
            for query in queries:
                if query.query == f"{search}":
                    for result in query.results:
                        if result.range["start"]["line"] == line:
                            kw_res = result.message
                            break
                    break
            res.append(kw_res)
            line += 1

        return tuple(res)

    def get_queries(self, coq_lsp_client, textDocument, keyword):
        """
        keyword might be Search, Print, Check, etc...
        """
        uri = textDocument.uri
        if textDocument.uri.startswith("file://"):
            uri = uri[7:]

        with open(uri, "r") as doc:
            if textDocument.uri not in coq_lsp_client.lsp_endpoint.diagnostics:
                return []
            lines = doc.readlines()
            diagnostics = coq_lsp_client.lsp_endpoint.diagnostics[textDocument.uri]
            searches = {}

            for diagnostic in diagnostics:
                command = lines[
                    diagnostic.range["start"]["line"] : diagnostic.range["end"]["line"]
                    + 1
                ]
                if len(command) == 1:
                    command[0] = command[0][
                        diagnostic.range["start"]["character"] : diagnostic.range[
                            "end"
                        ]["character"]
                        + 1
                    ]
                else:
                    command[0] = command[0][diagnostic.range["start"]["character"] :]
                    command[-1] = command[-1][
                        : diagnostic.range["end"]["character"] + 1
                    ]
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

    def has_error(self, textDocument):
        uri = textDocument.uri
        if textDocument.uri.startswith("file://"):
            uri = uri[7:]

        if textDocument.uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return False

        diagnostics = self.coq_lsp_client.lsp_endpoint.diagnostics[textDocument.uri]
        for diagnostic in diagnostics:
            if diagnostic.severity == 1:
                return True
        return False

    def __compute(self, search, line):
        res = self.__get_diagnostics(
            self.coq_lsp_client,
            self.aux_path,
            ("Locate", "Print", "Compute"),
            f"{search}",
            line,
        )
        if res[0].split()[1].startswith("Coq.Init."):
            return None

        if res[1] is None:
            return None
        res_print = res[1].split()
        if res[2] is None:
            return " ".join(res_print)
        res_compute = res[2].split()
        if res_compute[1] == search and res_print[1] != search:
            return " ".join(res_compute[1:])

        return " ".join(res_print)

    def __locate(self, search, line):
        nots = self.__get_diagnostics(
            self.coq_lsp_client, self.aux_path, ("Locate",), f'"{search}"', line
        )[0].split("\n")
        fun = lambda x: x.endswith("(default interpretation)")
        if len(nots) > 1:
            return list(filter(fun, nots))[0][:-25]
        else:
            return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __step_context(self, module_path):
        def transverse_ast(el):
            if isinstance(el, dict):
                res = []
                for k, v in el.items():
                    res.extend(transverse_ast(k))
                    res.extend(transverse_ast(v))
                return res
            elif isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                id = ".".join([l[1] for l in el[1][1][::-1]] + [el[2][1]])
                return [(self.__get_term, id, module_path[:])]
            elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                line = len(self.aux_file_text.split("\n"))
                self.__command(("Locate",), f'"{el[2][1]}"')
                return [(self.__locate, el[2][1], line)] + transverse_ast(el[1:])
            elif isinstance(el, list):
                res = []
                for v in el:
                    res.extend(transverse_ast(v))
                return res

            return []

        if not self.in_proof:
            return None

        res, transversed = [], transverse_ast(self.current_step)
        [res.append(x) for x in transversed if x not in res]
        return res

    def __step_goals(self):
        uri = "file://" + self.path
        start_line = self.current_step["range"]["end"]["line"]
        start_character = self.current_step["range"]["end"]["character"]
        end_pos = Position(start_line, start_character)
        return self.coq_lsp_client.proof_goals(TextDocumentIdentifier(uri), end_pos)

    def __step_text(self, start_line, start_character):
        end_line = self.current_step["range"]["end"]["line"]
        end_character = self.current_step["range"]["end"]["character"]
        lines = self.lines[start_line : end_line + 1]
        lines[-1] = lines[-1][: end_character + 1]
        lines[0] = lines[0][start_character:]
        return "\n".join(lines)

    def exec(self, steps=1):
        for _ in range(steps):
            if self.current_step != None:
                end_previous = (
                    self.current_step["range"]["end"]["line"],
                    self.current_step["range"]["end"]["character"],
                )
            else:
                end_previous = (0, 0)

            if len(self.ast) == 0:
                self.in_proof = False
                break
            self.current_step = self.ast.pop(0)

            text = self.__step_text(end_previous[0], end_previous[1])
            self.__write_on_aux_file(text)

            expr = self.__get_expr(self.current_step)
            if expr[0] == "VernacProof" or (
                expr[0] == "VernacExtend" and expr[1][0] == "Obligations"
            ):
                self.in_proof = True
            elif expr[0] == "VernacEndProof":
                self.in_proof = False

    def __next_steps(self, module_path):
        if not self.in_proof:
            return None

        aux_steps = []
        while self.in_proof:
            goals = self.__step_goals()
            line = self.current_step["range"]["end"]["line"]
            character = self.current_step["range"]["end"]["character"]

            self.exec()
            context_calls = self.__step_context(module_path)
            text = self.__step_text(line, character)
            aux_steps.append((text, goals, context_calls))

        return aux_steps

    def get_current_theorem(self):
        expr = self.__get_expr(self.current_step)
        if expr[0] != "VernacStartTheoremProof":
            return None
        name = self.__get_theorem_name(expr)
        return self.__compute(name)

    def jump_to_theorem(self):
        while self.__get_expr(self.current_step)[0] != "VernacStartTheoremProof":
            self.exec()
        return self.get_current_theorem()

    def jump_to_proof(self):
        while not self.in_proof and len(self.ast) > 0:
            self.exec()

    def __get_term(self, name, module_path):
        for i in range(len(module_path), -1, -1):
            cur_name = ".".join(module_path[:i] + [name])
            if cur_name in self.terms:
                return self.terms[cur_name]
            elif cur_name in self.alias_terms:
                return self.terms[self.alias_terms[cur_name]]
        return None

    def __add_alias(self, name, file_modules):
        current_file_module_path = ""
        for module in file_modules[::-1]:
            current_file_module_path = module + "." + current_file_module_path
            self.alias_terms[current_file_module_path + name] = name

    def __process_step(self, module_path, file_modules=[], step=None, lines=None):
        def step_text(step, lines):
            start_line = step["range"]["start"]["line"]
            start_character = step["range"]["start"]["character"]
            end_line = step["range"]["end"]["line"]
            end_character = step["range"]["end"]["character"]
            lines = lines[start_line : end_line + 1]
            lines[-1] = lines[-1][: end_character + 1]
            lines[0] = lines[0][start_character:]
            return " ".join("\n".join(lines).split())

        def transverse_ast(el, inductive=False):
            if isinstance(el, dict):
                if "v" in el and isinstance(el["v"], list) and len(el["v"]) == 2:
                    if el["v"][0] == "Id":
                        return [el["v"][1]]
                    if el["v"][0] == "Name":
                        return [el["v"][1][1]]

                res = []
                for k, v in el.items():
                    res.extend(transverse_ast(k, inductive))
                    res.extend(transverse_ast(v, inductive))
                return res
            elif isinstance(el, list):
                if len(el) > 0:
                    if el[0] == "CLocalAssum":
                        return []
                    if el[0] == "VernacInductive":
                        inductive = True

                res = []
                for v in el:
                    res.extend(transverse_ast(v, inductive))
                    if not inductive and len(res) > 0:
                        return res
                return res

            return []

        if step is None and lines is None:
            step, lines = self.current_step, self.lines

        text = step_text(step, lines)
        for keyword in ["Local", "Variable", "Let", "Context"]:
            if text.startswith(keyword):
                return module_path
        expr = self.__get_expr(step)
        if expr == [None]:
            return module_path

        full_name = lambda name: ".".join(module_path + [name])
        if (
            len(expr) >= 2
            and isinstance(expr[1], list)
            and len(expr[1]) == 2
            and expr[1][0] == "VernacDeclareTacticDefinition"
        ):
            name = expr[2][0][2][0][1][0][1][1]
            self.terms[full_name(name)] = text
            self.__add_alias(name, file_modules)
        elif expr[0] == "VernacNotation":
            self.notations.append(text)
        elif expr[0] == "VernacDefineModule":
            module_path.append(expr[2]["v"][1])
        elif expr[0] == "VernacEndSegment":
            if [expr[1]["v"][1]] == module_path[-1:]:
                module_path.pop()
        elif expr[0] != "VernacBeginSection":
            names = transverse_ast(expr)
            for name in names:
                self.terms[full_name(name)] = text
                self.__add_alias(name, file_modules)

        return module_path

    def __get_path_modules(self, file_path):
        modules = []
        if os.path.join("default", "lib", "coq") in file_path:
            modules.append("Coq")
        modules.extend(
            filter(lambda f: len(f) > 0 and f[0].isupper(), file_path.split(os.sep))
        )
        # File
        if len(modules) > 0 and modules[-1].endswith(".v"):
            modules[-1] = modules[-1][:-2]
        return modules

    def __get_symbols_library(self, file_path):
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)

        file_uri = f"file://{new_path}"
        file_modules = self.__get_path_modules(file_path)
        coq_lsp_client = CoqLspClient(
            file_uri, timeout=self.coq_lsp_client.lsp_endpoint.timeout
        )
        try:
            with open(new_path, "r") as f:
                lines = f.read().split("\n")
                coq_lsp_client.didOpen(
                    TextDocumentItem(file_uri, "coq", 1, "\n".join(lines))
                )
            ast = coq_lsp_client.get_document(TextDocumentIdentifier(file_uri))
            module_path = []
            for step in ast["spans"]:
                module_path = self.__process_step(
                    module_path, file_modules=file_modules, step=step, lines=lines
                )
        finally:
            os.remove(new_path)
            coq_lsp_client.shutdown()
            coq_lsp_client.exit()

    def __get_libraries(self):
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(self.path, new_path)

        file_uri = f"file://{new_path}"
        coq_lsp_client = CoqLspClient(file_uri)
        coq_lsp_client.lsp_endpoint.timeout = self.coq_lsp_client.lsp_endpoint.timeout
        try:
            with open(new_path, "a") as f:
                f.write("\nPrint Libraries.")
            with open(new_path, "r") as f:
                lines = f.read().split("\n")
                coq_lsp_client.didOpen(
                    TextDocumentItem(file_uri, "coq", 1, "\n".join(lines))
                )
                last_line = len(lines) - 1
            libraries = self.__get_diagnostics(
                coq_lsp_client, new_path, ("Print Libraries",), "", last_line
            )[0]
            libraries = list(
                map(lambda line: line.strip(), libraries.split("\n")[1:-1])
            )
            with open(new_path, "a") as f:
                for library in libraries:
                    lines.append(f"Locate Library {library}.")
                    f.write(f"\nLocate Library {library}.")
            coq_lsp_client.didChange(
                VersionedTextDocumentIdentifier(file_uri, 2),
                [TextDocumentContentChangeEvent(None, None, "\n".join(lines))],
            )
            for i, library in enumerate(libraries):
                v_file = self.__get_diagnostics(
                    coq_lsp_client,
                    new_path,
                    ("Locate Library",),
                    library,
                    last_line + i + 1,
                )[0]
                v_file = v_file.split("\n")[-1][:-1]
                self.__get_symbols_library(v_file)

            # Get symbols from own file
            self.__get_symbols_library(self.path)
        finally:
            os.remove(new_path)
            coq_lsp_client.shutdown()
            coq_lsp_client.exit()

    def proof_steps(self):
        aux_proofs = []
        module_path = []

        self.__get_libraries()
        while len(self.ast) > 0:
            self.exec()
            if self.in_proof:
                aux_proofs.append(self.__next_steps(module_path))
            else:
                module_path = self.__process_step(module_path)
        self.__call_didOpen()

        proofs = []
        for aux_proof_steps in aux_proofs:
            proof_steps = []
            for step in aux_proof_steps:
                context = []
                if step[2] is None:
                    context = None
                else:
                    for context_call in step[2]:
                        context.append(context_call[0](*context_call[1:]))
                    filtered, context = filter(lambda x: x is not None, context), []
                    [context.append(x) for x in filtered if x not in context]
                proof_steps.append(Step(step[0], step[1], context))
            proofs.append(proof_steps)

        return proofs

    def is_invalid(self):
        uri = f"file://{self.path}"
        return self.has_error(TextDocumentIdentifier(uri))

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.aux_path)
