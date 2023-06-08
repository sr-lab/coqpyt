import os
import pytest
from pylspclient.lsp_structs import *
from pylspclient.coq_lsp_structs import *
from pylspclient.coq_lsp_client import CoqLspClient
from pylspclient.proof_state import ProofState

root_path: str = None
root_uri: str = None
lsp_client: CoqLspClient = None
state: ProofState = None

@pytest.fixture
def setup(request):
    global root_path, root_uri, lsp_client, state, versionId
    root_path = "tests/resources"
    root_uri = 'file://' + root_path
    lsp_client = CoqLspClient(root_uri)

    file_path = os.path.join(root_path, request.param)
    uri = "file://" + file_path
    text = open(file_path, "r").read()
    lsp_client.didOpen(TextDocumentItem(uri, 'coq', 1, text))
    ast = lsp_client.get_document(TextDocumentIdentifier(uri))
    state = ProofState(lsp_client, file_path, ast)
    versionId = VersionedTextDocumentIdentifier(uri, 1)
    yield

@pytest.fixture
def teardown():
    yield
    lsp_client.shutdown()
    lsp_client.exit()

@pytest.mark.parametrize('setup', ['test_next_steps.v'], indirect=True)
def test_next_steps(setup, teardown):
    texts = [
        '\n      intros n.',
        '\n      Print plus.',
        '\n      Print Nat.add.',
        '\n      reduce_eq.',
        '\n    Qed.'
    ]
    goals = [
        GoalAnswer(versionId, Position(7, 10), [], GoalConfig([Goal([], '∀ n : nat, 0 + n = n')], [], [], [], None)),
        GoalAnswer(versionId, Position(8, 15), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], '0 + n = n')], [], [], [], None)),
        GoalAnswer(versionId, Position(9, 17), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], '0 + n = n')], [], [], [], None)),
        GoalAnswer(versionId, Position(10, 20), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], '0 + n = n')], [], [], [], None)),
        GoalAnswer(versionId, Position(11, 16), [], GoalConfig([], [], [], [], None))
    ]
    contexts = [
        [],
        ['Notation plus := Nat.add'],
        ['Nat.add = fix add (n m : nat) {struct n} : nat := match n with | 0 => m | S p => S (add p m) end : nat → nat → nat Arguments Nat.add (n m)%nat_scope'],
        ['Ltac reduce_eq := simpl; reflexivity'],
        None
    ]
    
    state.jump_to_proof()
    next_steps = state.next_steps()
    assert len(next_steps) == 5
    for i in range(5):
        assert next_steps[i].text == texts[i]
        assert str(next_steps[i].goals) == str(goals[i])
        assert next_steps[i].context == contexts[i]


    texts = [
        '\n  intros n m.',
        '\n  rewrite -> (Out.In.plus_O_n (S n * m)).',
        '\n  Compute True /\\ True.',
        '\n  reflexivity.',
        '\nQed.'
    ]
    goals = [
        GoalAnswer(versionId, Position(21, 6), [], GoalConfig([Goal([], '∀ n m : nat, 0 + S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(22, 13), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], '0 + S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(23, 41), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(24, 23), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(25, 14), [], GoalConfig([], [], [], [], None))
    ]
    contexts = [
        [],
        ['Out.In.plus_O_n : ∀ n : nat, 0 + n = n', 'Notation "x * y" := (Nat.mul x y) : nat_scope', 'Inductive nat : Set := O : nat | S : nat → nat. Arguments S _%nat_scope'],
        ['Notation "A /\\ B" := (and A B) : type_scope', 'Inductive True : Prop := I : True.'],
        ['Ltac reflexivity := <coq-core.plugins.ltac::reflexivity@0>'],
        None
    ]

    state.jump_to_proof()
    next_steps = state.next_steps()
    assert len(next_steps) == 5
    for i in range(5):
        assert next_steps[i].text == texts[i]
        assert str(next_steps[i].goals) == str(goals[i])
        assert next_steps[i].context == contexts[i]
