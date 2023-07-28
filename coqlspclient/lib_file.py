import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import TextDocumentItem, VersionedTextDocumentIdentifier, TextDocumentContentChangeEvent
from pylspclient.lsp_structs import ResponseError, ErrorCodes
from coqlspclient.coq_lsp_structs import Result, Query
from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_file import CoqFile
from typing import Dict, List


class LibFile(object):
    def __init__(self, file_path: str, timeout: int = 2):
        self.__init_path(file_path)
        file_uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(file_uri, timeout=timeout)
        try:
            with open(self.path, "a") as f:
                f.write("\nPrint Libraries.")
            with open(self.path, "r") as f:
                self.lines = f.read().split("\n")
                self.coq_lsp_client.didOpen(
                    TextDocumentItem(file_uri, "coq", 1, "\n".join(self.lines))
                )
            self.terms: Dict[str, str] = {}
            self.aliases: Dict[str, str] = {}
            self.notations: List[str] = []
            self.__get_libraries()
        except Exception as e:
            if not (
                isinstance(e, ResponseError)
                and e.code == ErrorCodes.ServerQuit.value
            ):
                self.coq_lsp_client.shutdown()
                self.coq_lsp_client.exit()
            os.remove(self.path)
            raise e

    def __init_path(self, file_path):
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        shutil.copyfile(file_path, new_path)
        self.path = new_path

    def __get_queries(self, keyword):
        uri = f"file://{self.path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return []
        
        searches = {}
        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            command = self.lines[
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
    
    def __get_symbols_library(self, file_path):
        coq_file = CoqFile(file_path, timeout=self.coq_lsp_client.lsp_endpoint.timeout)
        coq_file.run()
        self.terms.update(coq_file.terms)
        self.aliases.update(coq_file.aliases)
        self.notations.extend(coq_file.notations)
        coq_file.close()
    
    def __get_libraries(self):
        last_line = len(self.lines) - 1
        libraries = self.__get_diagnostics("Print Libraries", "", last_line)
        libraries = list(map(lambda line: line.strip(), libraries.split("\n")[1:-1]))
        with open(self.path, "a") as f:
            for library in libraries:
                self.lines.append(f"Locate Library {library}.")
                f.write(f"\nLocate Library {library}.")

        uri = f"file://{self.path}"
        self.coq_lsp_client.didChange(
            VersionedTextDocumentIdentifier(uri, 2),
            [TextDocumentContentChangeEvent(None, None, "\n".join(self.lines))],
        )
        for i, library in enumerate(libraries):
            v_file = self.__get_diagnostics("Locate Library", library, last_line + i + 1)
            v_file = v_file.split("\n")[-1][:-1]
            self.__get_symbols_library(v_file)

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.path)