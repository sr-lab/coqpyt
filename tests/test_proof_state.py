import os
import pytest
from pylspclient.lsp_structs import *
from pylspclient.coq_lsp_structs import *
from pylspclient.proof_state import ProofState

versionId: VersionedTextDocumentIdentifier = None
state: ProofState = None

@pytest.fixture
def setup(request):
    global lsp_client, state, versionId
    file_path = os.path.join("tests/resources", request.param)
    uri = "file://" + file_path
    state = ProofState(file_path)
    versionId = VersionedTextDocumentIdentifier(uri, 1)
    yield

@pytest.fixture
def teardown():
    yield
    state.close()

@pytest.mark.parametrize('setup', ['test_proof_steps.v'], indirect=True)
def test_proof_steps(setup, teardown):
    proof_steps = state.proof_steps()
    assert len(proof_steps) == 10

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
    
    for i in range(5):
        assert proof_steps[i].text == texts[i]
        assert str(proof_steps[i].goals) == str(goals[i])
        assert proof_steps[i].context == contexts[i]

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

    for i in range(5, 10):
        assert proof_steps[i].text == texts[i - 5]
        assert str(proof_steps[i].goals) == str(goals[i - 5])
        assert proof_steps[i].context == contexts[i - 5]
