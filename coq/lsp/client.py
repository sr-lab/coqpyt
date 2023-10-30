import time
import subprocess
from lsp.json_rpc_endpoint import JsonRpcEndpoint
from lsp.endpoint import LspEndpoint
from lsp.client import LspClient
from lsp.structs import *
from coq.lsp.structs import *


class CoqLspClient(LspClient):
    """Abstraction to interact with coq-lsp

    Attributes:
        file_progress (Dict[str, List[CoqFileProgressParams]]): Contains all
            the `$/coq/fileProgress` notifications sent by the server. The
            keys are the URIs of the files and the values are the list of
            notifications.
    """

    __DEFAULT_INIT_OPTIONS = {
        "max_errors": 120000000,
        "show_coq_info_messages": True,
    }

    def __init__(
        self,
        root_uri: str,
        timeout: int = 30,
        memory_limit: int = 2097152,
        init_options: Dict = __DEFAULT_INIT_OPTIONS,
    ):
        """Creates a CoqLspClient

        Args:
            root_uri (str): URI to the workspace where coq-lsp will run
                The URI can be either a file or a folder.
            timeout (int, optional): Timeout used for the coq-lsp operations.
                Defaults to 2.
            memory_limit (int, optional): RAM limit for the coq-lsp process
                in kbytes. Defaults to 2097152.
            init_options (Dict, optional): Initialization options for coq-lsp server.
                Available options are:
                    max_errors (int): Maximum number of errors per file, after that,
                        coq-lsp will stop checking the file. Defaults to 120000000.
                    show_coq_info_messages (bool): Show Coq's info messages as diagnostics.
                        Defaults to false.
                    show_notices_as_diagnostics (bool): Show Coq's notice messages
                        as diagnostics, such as `About` and `Search` operations.
                        Defaults to false.
                    debug (bool): Enable Debug in Coq Server. Defaults to false.
                    pp_type (int): Method to print Coq Terms.
                        0 = Print to string
                        1 = Use jsCoq's Pp rich layout printer
                        2 = Coq Layout Engine
                        Defaults to 1.
        """
        self.file_progress: Dict[str, List[CoqFileProgressParams]] = {}
        proc = subprocess.Popen(
            f"ulimit -v {memory_limit}; coq-lsp",
            stdout=subprocess.PIPE,
            stdin=subprocess.PIPE,
            shell=True,
        )
        json_rpc_endpoint = JsonRpcEndpoint(proc.stdin, proc.stdout)
        lsp_endpoint = LspEndpoint(json_rpc_endpoint, timeout=timeout)
        lsp_endpoint.notify_callbacks = {
            "$/coq/fileProgress": self.__handle_file_progress,
            "textDocument/publishDiagnostics": self.__handle_publish_diagnostics,
        }
        super().__init__(lsp_endpoint)
        workspaces = [{"name": "coq-lsp", "uri": root_uri}]
        # This is required to be False since we use it to know if operations
        # such as didOpen and didChange already finished.
        init_options["eager_diagnostics"] = False
        self.initialize(
            proc.pid,
            "",
            root_uri,
            init_options,
            {},
            "off",
            workspaces,
        )
        self.initialized()
        # Used to check if didOpen and didChange already finished
        self.__completed_operation = False

    def __handle_publish_diagnostics(self, params: Dict):
        self.__completed_operation = True

    def __handle_file_progress(self, params: Dict):
        coqFileProgressKind = CoqFileProgressParams.parse(params)
        uri = coqFileProgressKind.textDocument.uri
        if uri not in self.file_progress:
            self.file_progress[uri] = [coqFileProgressKind]
        else:
            self.file_progress[uri].append(coqFileProgressKind)

    def __wait_for_operation(self):
        timeout = self.lsp_endpoint.timeout
        while not self.__completed_operation and timeout > 0:
            if self.lsp_endpoint.shutdown_flag:
                raise ResponseError(ErrorCodes.ServerQuit, "Server quit")
            time.sleep(0.1)
            timeout -= 0.1

        if timeout <= 0:
            self.shutdown()
            self.exit()
            raise ResponseError(ErrorCodes.ServerTimeout, "Server timeout")

    def didOpen(self, textDocument: TextDocumentItem):
        """Open a text document in the server.

        Args:
            textDocument (TextDocumentItem): Text document to open
        """
        self.__completed_operation = False
        self.lsp_endpoint.diagnostics[textDocument.uri] = []
        super().didOpen(textDocument)
        self.__wait_for_operation()

    def didChange(
        self,
        textDocument: VersionedTextDocumentIdentifier,
        contentChanges: list[TextDocumentContentChangeEvent],
    ):
        """Submit changes on a text document already open on the server.

        Args:
            textDocument (VersionedTextDocumentIdentifier): Text document changed.
            contentChanges (list[TextDocumentContentChangeEvent]): Changes made.
        """
        self.__completed_operation = False
        self.lsp_endpoint.diagnostics[textDocument.uri] = []
        super().didChange(textDocument, contentChanges)
        self.__wait_for_operation()

    def proof_goals(
        self, textDocument: TextDocumentIdentifier, position: Position
    ) -> Optional[GoalAnswer]:
        """Get proof goals and relevant information at a position.

        Args:
            textDocument (TextDocumentIdentifier): Text document to consider.
            position (Position): Position used to get the proof goals.

        Returns:
            GoalAnswer: Contains the goals at a position, messages associated
                to the position and if errors exist, the top error at the position.
        """
        result_dict = self.lsp_endpoint.call_method(
            "proof/goals", textDocument=textDocument, position=position
        )
        return GoalAnswer.parse(result_dict)

    def get_document(
        self, textDocument: TextDocumentIdentifier
    ) -> Optional[FlecheDocument]:
        """Get the AST of a text document.

        Args:
            textDocument (TextDocumentIdentifier): Text document

        Returns:
            Optional[FlecheDocument]: Serialized version of Fleche's document
        """
        result_dict = self.lsp_endpoint.call_method(
            "coq/getDocument", textDocument=textDocument
        )
        return FlecheDocument.parse(result_dict)

    def save_vo(self, textDocument: TextDocumentIdentifier):
        """Save a compiled file to disk.

        Args:
            textDocument (TextDocumentIdentifier): File to be saved.
                The uri in the textDocument should contain an absolute path.
        """
        self.lsp_endpoint.call_method("coq/saveVo", textDocument=textDocument)

    # TODO: handle performance data notification?
