import os
import shutil
import uuid
import tempfile
from pylspclient.lsp_structs import (
    TextDocumentItem,
    VersionedTextDocumentIdentifier,
    TextDocumentContentChangeEvent,
)
from pylspclient.lsp_structs import ResponseError, ErrorCodes
from coqlspclient.coq_lsp_structs import Result, Query, FileContext
from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_file import CoqFile
from typing import Optional


class AuxFile(object):
    def __init__(self, file_path: Optional[str] = None, timeout: int = 2):
        self.__init_path(file_path)
        uri = f"file://{self.path}"
        self.coq_lsp_client = CoqLspClient(uri, timeout=timeout)

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __init_path(self, file_path):
        temp_dir = tempfile.gettempdir()
        new_path = os.path.join(
            temp_dir, "aux_" + str(uuid.uuid4()).replace("-", "") + ".v"
        )
        with open(new_path, "w"):
            # Create empty file
            pass

        if file_path is not None:
            shutil.copyfile(file_path, new_path)

        self.path = new_path
        self.version = 1

    def read(self):
        with open(self.path, "r") as f:
            return f.read()

    def write(self, text):
        with open(self.path, "w") as f:
            f.write(text)

    def append(self, text):
        with open(self.path, "a") as f:
            f.write(text)

    def __handle_exception(self, e):
        if not (isinstance(e, ResponseError) and e.code == ErrorCodes.ServerQuit.value):
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
        os.remove(self.path)

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

    def __get_queries(self, keyword):
        uri = f"file://{self.path}"
        if uri not in self.coq_lsp_client.lsp_endpoint.diagnostics:
            return []

        searches = {}
        lines = self.read().split("\n")
        for diagnostic in self.coq_lsp_client.lsp_endpoint.diagnostics[uri]:
            command = lines[
                diagnostic.range["start"]["line"] : diagnostic.range["end"]["line"] + 1
            ]
            if len(command) == 1:
                command[0] = command[0][
                    diagnostic.range["start"]["character"] : diagnostic.range["end"][
                        "character"
                    ]
                    + 1
                ]
            else:
                command[0] = command[0][diagnostic.range["start"]["character"] :]
                command[-1] = command[-1][: diagnostic.range["end"]["character"] + 1]
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
                    if result.range["start"]["line"] == line:
                        return result.message
                break
        return None

    def close(self):
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()
        os.remove(self.path)

    @staticmethod
    def get_context(file_path: str, timeout: int):
        aux_file = AuxFile(file_path=file_path, timeout=timeout)
        aux_file.append("\nPrint Libraries.")
        aux_file.didOpen()

        last_line = len(aux_file.read().split("\n")) - 1
        libraries = aux_file.get_diagnostics("Print Libraries", "", last_line)
        libraries = list(map(lambda line: line.strip(), libraries.split("\n")[1:-1]))
        for library in libraries:
            aux_file.append(f"\nLocate Library {library}.")
        aux_file.didChange()

        context = FileContext()
        for i, library in enumerate(libraries):
            v_file = aux_file.get_diagnostics(
                "Locate Library", library, last_line + i + 1
            ).split("\n")[-1][:-1]
            coq_file = CoqFile(v_file, library=library, timeout=timeout)
            coq_file.run()
            context.update(**vars(coq_file.context))
            coq_file.close()

        aux_file.close()
        return context
