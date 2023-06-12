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
    assert len(proof_steps) == 4

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
        assert proof_steps[0][i].text == texts[i]
        assert str(proof_steps[0][i].goals) == str(goals[i])
        assert proof_steps[0][i].context == contexts[i]

    texts = [
        '\n  intros n m.',
        '\n  rewrite -> (plus_O_n (S n * m)).',
        '\n  Compute True /\\ True.',
        '\n  reflexivity.',
        '\nQed.'
    ]
    goals = [
        GoalAnswer(versionId, Position(18, 6), [], GoalConfig([Goal([], '∀ n m : nat, 0 + S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(19, 13), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], '0 + S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(20, 34), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(21, 23), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(22, 14), [], GoalConfig([], [], [], [], None))
    ]
    contexts = [
        [],
        ['plus_O_n : ∀ n : nat, 0 + n = n', 'Notation "x * y" := (Nat.mul x y) : nat_scope', 'Inductive nat : Set := O : nat | S : nat → nat. Arguments S _%nat_scope'],
        ['Notation "A /\\ B" := (and A B) : type_scope', 'Inductive True : Prop := I : True.'],
        ['Ltac reflexivity := <coq-core.plugins.ltac::reflexivity@0>'],
        None
    ]

    for i in range(5):
        assert proof_steps[1][i].text == texts[i]
        assert str(proof_steps[1][i].goals) == str(goals[i])
        assert proof_steps[1][i].context == contexts[i]

    texts = [
        '\n    intros n.',
        '\n    Compute mk_example n n.',
        '\n    Compute {| fst := n; snd := n |}.',
        '\n    reduce_eq.',
        '\n  Qed.'
    ]
    goals = [
        GoalAnswer(versionId, Position(29, 8), [], GoalConfig([Goal([], '∀ n : nat, n = 0 + n')], [], [], [], None)),
        GoalAnswer(versionId, Position(30, 13), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], 'n = 0 + n')], [], [], [], None)),
        GoalAnswer(versionId, Position(31, 27), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], 'n = 0 + n')], [], [], [], None)),
        GoalAnswer(versionId, Position(32, 37), [], GoalConfig([Goal([Hyp(['n'], 'nat', None)], 'n = 0 + n')], [], [], [], None)),
        GoalAnswer(versionId, Position(33, 14), [], GoalConfig([], [], [], [], None))
    ]
    contexts = [
        [],
        ['Record example : Set := mk_example { fst : nat; snd : nat }. Arguments mk_example (fst snd)%nat_scope'],
        ['fst = λ e : example, let (fst, _) := e in fst : example → nat Arguments fst e', 'snd = λ e : example, let (_, snd) := e in snd : example → nat Arguments snd e'],
        ['Ltac reduce_eq := simpl; reflexivity'],
        None
    ]
    
    for i in range(5):
        assert proof_steps[2][i].text == texts[i]
        assert str(proof_steps[2][i].goals) == str(goals[i])
        assert proof_steps[2][i].context == contexts[i]

    texts = [
        '\n    intros n m.',
        '\n    rewrite <- (plus_O_n (S n * m)).',
        '\n    Compute Out.In.plus_O_n.',
        '\n    reflexivity.',
        '\n  Qed.'
    ]
    goals = [
        GoalAnswer(versionId, Position(38, 8), [], GoalConfig([Goal([], '∀ n m : nat, S n * m = 0 + S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(39, 15), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = 0 + S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(40, 36), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(41, 28), [], GoalConfig([Goal([Hyp(['n', 'm'], 'nat', None)], 'S n * m = S n * m')], [], [], [], None)),
        GoalAnswer(versionId, Position(42, 16), [], GoalConfig([], [], [], [], None))
    ]
    contexts = [
        [],
        ['plus_O_n : ∀ n : nat, n = 0 + n', 'Notation "x * y" := (Nat.mul x y) : nat_scope', 'Inductive nat : Set := O : nat | S : nat → nat. Arguments S _%nat_scope'],
        ['Out.In.plus_O_n : ∀ n : nat, 0 + n = n'],
        ['Ltac reflexivity := <coq-core.plugins.ltac::reflexivity@0>'],
        None
    ]

    for i in range(5):
        assert proof_steps[3][i].text == texts[i]
        assert str(proof_steps[3][i].goals) == str(goals[i])
        assert proof_steps[3][i].context == contexts[i]

@pytest.mark.parametrize('setup', ['test_is_invalid_1.v'], indirect=True)
def test_is_invalid_1(setup, teardown):
    found_error = state.is_invalid()
    assert found_error == True

@pytest.mark.parametrize('setup', ['test_is_invalid_2.v'], indirect=True)
def test_is_invalid_2(setup, teardown):
    found_error = state.is_invalid()
    assert found_error == True

@pytest.mark.parametrize('setup', ['test_is_valid.v'], indirect=True)
def test_is_valid(setup, teardown):
    found_error = state.is_invalid()
    assert found_error == False