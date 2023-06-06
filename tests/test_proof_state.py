import os
import pytest
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.coq_lsp_client import CoqLspClient
from pylspclient.proof_state import ProofState

root_path: str = None
root_uri: str = None
lsp_client: CoqLspClient = None
state: ProofState = None

@pytest.fixture
def setup(request):
    global root_path, root_uri, lsp_client, state
    root_path = "tests/resources"
    root_uri = 'file://' + root_path
    lsp_client = CoqLspClient(root_uri)

    file_path = os.path.join(root_path, request.param)
    uri = "file://" + file_path
    text = open(file_path, "r").read()
    lsp_client.didOpen(TextDocumentItem(uri, 'coq', 1, text))
    ast = lsp_client.get_document(TextDocumentIdentifier(uri))
    state = ProofState(lsp_client, file_path, ast)
    yield

@pytest.fixture
def teardown():
    yield
    lsp_client.shutdown()
    lsp_client.exit()

@pytest.mark.parametrize('setup', ['test_next_steps.v'], indirect=True)
def test_next_steps(setup, teardown):
    state.jump_to_proof()
    next_steps = """\n  intros n.
  Print plus.
  Print Nat.add.
  simpl.
  reflexivity.
Qed."""
    assert state.next_steps()[0] == next_steps
    assert len(state.next_steps()[1]) == 6

@pytest.mark.parametrize('setup', ['test_proof_context.v'], indirect=True)
def test_proof_context(setup, teardown):
    state.jump_to_proof()
    state.jump_to_theorem()
    state.jump_to_proof()

    proof_context = state.get_proof_context()
    assert len(proof_context) == 3
    assert 'Out.In.plus_O_n\n     : ∀ n : nat, 0 + n = n' in proof_context
    assert 'Notation "x * y" := (Nat.mul x y) : nat_scope' in proof_context
    assert 'Notation "A /\\ B" := (and A B) : type_scope' in proof_context
