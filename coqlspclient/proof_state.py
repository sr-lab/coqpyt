import os
import uuid
from pylspclient.lsp_structs import TextDocumentItem
from coqlspclient.coq_lsp_structs import ProofStep, Result, Query
from coqlspclient.coq_lsp_structs import CoqError, CoqErrorCodes
from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.lib_file import LibFile
from coqlspclient.coq_file import CoqFile


class ProofState(object):
    def __init__(self, file_path, timeout=2):
        self.coq_file = CoqFile(file_path, timeout=timeout)
        if not self.coq_file.is_valid:
            self.coq_file.close()
            raise CoqError(CoqErrorCodes.InvalidFile, f"More than one error found in file {file_path}")
        self.current_step = None
        self.__init_aux_file(file_path, timeout)

    def __init_aux_file(self, file_path, timeout):
        dir = os.path.dirname(file_path)
        new_base_name = os.path.basename(file_path).split(".")
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

        aux_uri = f"file://{self.aux_path}"
        self.coq_lsp_client = CoqLspClient(aux_uri, timeout=timeout)

    def __write_on_aux_file(self, text):
        self.aux_file_text += text
        with open(self.aux_path, "a") as f:
            f.write(text)

    def __call_didOpen(self):
        uri = f"file://{self.aux_path}"
        self.coq_lsp_client.didOpen(TextDocumentItem(uri, "coq", 1, self.aux_file_text))

    def __command(self, keyword, search):
        command = f"\n{keyword} {search}."
        self.__write_on_aux_file(command)

    def __get_queries(self, keyword):
        uri = f"file://{self.aux_path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return []
        
        searches = {}
        lines = self.aux_file_text.split("\n")
        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
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

    def __get_diagnostics(self, keyword, search, line):
        for query in self.__get_queries(keyword):
            if query.query == f"{search}":
                for result in query.results:
                    if result.range["start"]["line"] == line:
                        return result.message
                break
        return None

    def __locate(self, search, line):
        nots = self.__get_diagnostics("Locate", f'"{search}"', line).split("\n")
        fun = lambda x: x.endswith("(default interpretation)")
        if len(nots) > 1:
            return list(filter(fun, nots))[0][:-25]
        else:
            return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __get_term(self, name, curr_module):
        for i in range(len(curr_module), -1, -1):
            curr_name = ".".join(curr_module[:i] + [name])
            if curr_name in self.coq_file.terms:
                return self.coq_file.terms[curr_name]
            elif curr_name in self.coq_file.aliases:
                return self.coq_file.terms[self.coq_file.aliases[curr_name]]
        return None

    def __step_context(self):
        def traverse_ast(el):
            if isinstance(el, dict):
                res = []
                for k, v in el.items():
                    res.extend(traverse_ast(k))
                    res.extend(traverse_ast(v))
                return res
            elif isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                id = ".".join([l[1] for l in el[1][1][::-1]] + [el[2][1]])
                return [(self.__get_term, id, self.coq_file.curr_module[:])]
            elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                line = len(self.aux_file_text.split("\n"))
                self.__command("Locate", f'"{el[2][1]}"')
                return [(self.__locate, el[2][1], line)] + traverse_ast(el[1:])
            elif isinstance(el, list):
                res = []
                for v in el:
                    res.extend(traverse_ast(v))
                return res

            return []

        res, transversed = [], traverse_ast(self.current_step.ast.span)
        [res.append(x) for x in transversed if x not in res]
        return res

    def __step(self):
        self.current_step = self.coq_file.exec()[0]
        self.__write_on_aux_file(self.current_step.text)

    def __next_steps(self):
        def trim_step_text():
            range = self.current_step.ast.range
            nlines = range.end.line - range.start.line
            text = self.current_step.text.split("\n")[-nlines:]
            text[0] = text[0][range.start.character:]
            return "\n".join(text)

        aux_steps = []
        while self.coq_file.in_proof:
            goals = self.coq_file.current_goals()
            self.__step()
            text = trim_step_text()
            context_calls = self.__step_context()
            aux_steps.append((text, goals, context_calls))
        return aux_steps

    def __get_libraries(self):
        lib_file = LibFile(self.coq_file.path, timeout=self.coq_lsp_client.lsp_endpoint.timeout)
        self.coq_file.terms = lib_file.terms
        self.coq_file.aliases = lib_file.aliases
        self.coq_file.notations = lib_file.notations
        lib_file.close()

    def proof_steps(self):
        self.__get_libraries()

        aux_proofs = []
        while not self.coq_file.checked():
            self.__step()
            if self.coq_file.in_proof:
                aux_proofs.append(self.__next_steps())
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
                proof_steps.append(ProofStep(step[0], step[1], context))
            proofs.append(proof_steps)

        return proofs

    def close(self):
        self.coq_file.close()
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.aux_path)
