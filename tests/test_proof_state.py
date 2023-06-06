import os
import pytest
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.coq_lsp_client import CoqLspClient
from pylspclient.proof_state import ProofState

root_path = "tests/resources"
root_uri = 'file://' + root_path
lsp_client = CoqLspClient(root_uri)

@pytest.fixture
def teardown():
    yield
    lsp_client.shutdown()
    lsp_client.exit()

def test_next_steps(teardown):
    file_path = os.path.join(root_path, 'test.v')
    uri = "file://" + file_path
    text = open(file_path, "r").read()
    lsp_client.didOpen(TextDocumentItem(uri, 'coq', 1, text))
    ast = lsp_client.get_document(TextDocumentIdentifier(uri))
    state = ProofState(lsp_client, file_path, ast)

    state.jump_to_proof()
    next_steps = """\n  intros n.
  Print plus.
  Print Nat.add.
  simpl.
  reflexivity.
Qed."""
    assert state.next_steps() == next_steps



