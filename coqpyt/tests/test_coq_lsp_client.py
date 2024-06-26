import os

from coqpyt.lsp.structs import *
from coqpyt.coq.lsp.client import CoqLspClient


def test_save_vo():
    client = CoqLspClient("tests/resources")
    file_path = f"{os.getcwd()}/tests/resources/test_valid.v"
    uri = f"file://{os.getcwd()}/tests/resources/test_valid.v"
    with open(file_path, "r") as f:
        client.didOpen(TextDocumentItem(uri, "coq", 1, f.read()))
    versionId = TextDocumentIdentifier(uri)
    client.save_vo(versionId)
    client.shutdown()
    client.exit()
    assert os.path.exists("tests/resources/test_valid.vo")
    os.remove("tests/resources/test_valid.vo")
