import os
from pylspclient.coq_lsp_client import CoqLspClient
from pylspclient.lsp_structs import *
from pylspclient.coq_lsp_structs import *

def test_save_vo():
    client = CoqLspClient("tests/resources")
    file_path = f"{os.getcwd()}/tests/resources/test_proof_steps.v"
    uri = f"file://{os.getcwd()}/tests/resources/test_proof_steps.v"
    with open(file_path, 'r') as f:
        client.didOpen(TextDocumentItem(uri, 'coq', 1, f.read()))
    versionId = TextDocumentIdentifier(uri)
    client.save_vo(versionId)
    client.shutdown()
    client.exit()
    assert os.path.exists("tests/resources/test_proof_steps.vo")
    os.remove("tests/resources/test_proof_steps.vo")

