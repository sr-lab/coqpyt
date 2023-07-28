import os
import pytest
from coqlspclient.coq_lsp_structs import *
from coqlspclient.proof_state import ProofState

versionId: VersionedTextDocumentIdentifier = None
state: ProofState = None


@pytest.fixture
def setup(request):
    global state, versionId
    file_path = os.path.join("tests/resources", request.param)
    uri = "file://" + file_path
    state = ProofState(file_path, timeout=60)
    versionId = VersionedTextDocumentIdentifier(uri, 1)
    yield


@pytest.fixture
def teardown():
    yield
    state.close()


@pytest.mark.parametrize("setup", ["test_proof_steps.v"], indirect=True)
def test_proof_steps(setup, teardown):
    proof_steps = state.proof_steps()
    assert len(proof_steps) == 4

    texts = [
        "\n      intros n.",
        "\n      Print plus.",
        "\n      Print Nat.add.",
        "\n      reduce_eq.",
        "\n    Qed.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(9, 10),
            [],
            GoalConfig([Goal([], "∀ n : nat, 0 + n = n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(10, 15),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "0 + n = n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(11, 17),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "0 + n = n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(12, 20),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "0 + n = n")], [], [], []),
        ),
        GoalAnswer(versionId, Position(13, 16), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
        ["Notation plus := Nat.add (only parsing)."],
        [
            'Fixpoint add n m := match n with | 0 => m | S p => S (p + m) end where "n + m" := (add n m) : nat_scope.'
        ],
        ["Ltac reduce_eq := simpl; reflexivity."],
        [],
    ]

    for i in range(5):
        assert proof_steps[0][i].text == texts[i]
        assert str(proof_steps[0][i].goals) == str(goals[i])
        assert proof_steps[0][i].context == contexts[i]

    texts = [
        "\n    intros n m.",
        "\n    rewrite -> (plus_O_n (S n * m)).",
        "\n    Compute True /\\ True.",
        "\n    reflexivity.",
        "\n  Qed.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(21, 8),
            [],
            GoalConfig([Goal([], "∀ n m : nat, 0 + S n * m = S n * m")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(22, 15),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "0 + S n * m = S n * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(
            versionId,
            Position(23, 36),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "S n * m = S n * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(
            versionId,
            Position(24, 25),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "S n * m = S n * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(versionId, Position(25, 16), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
        [
            "Lemma plus_O_n : forall n:nat, 0 + n = n.",
            'Notation "x * y" := (Nat.mul x y) : nat_scope',
            "Inductive nat : Set := | O : nat | S : nat -> nat.",
        ],
        [
            'Notation "A /\\ B" := (and A B) : type_scope',
            "Inductive True : Prop := I : True.",
        ],
        [],
        [],
    ]

    for i in range(5):
        assert proof_steps[1][i].text == texts[i]
        assert str(proof_steps[1][i].goals) == str(goals[i])
        assert proof_steps[1][i].context == contexts[i]

    texts = [
        "\n      intros n.",
        "\n      Compute mk_example n n.",
        "\n      Compute Out.In.plus_O_n.",
        "\n      reduce_eq.",
        "\n    Qed.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(34, 10),
            [],
            GoalConfig([Goal([], "∀ n : nat, n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(35, 15),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(36, 29),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(37, 30),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(versionId, Position(38, 16), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
        ["Record example := mk_example { fst : nat; snd : nat }."],
        ["Theorem plus_O_n : forall n:nat, 0 + n = n."],
        ["Ltac reduce_eq := simpl; reflexivity."],
        [],
    ]

    for i in range(5):
        assert proof_steps[2][i].text == texts[i]
        assert str(proof_steps[2][i].goals) == str(goals[i])
        assert proof_steps[2][i].context == contexts[i]

    texts = [
        "\n      intros n m.",
        "\n      rewrite <- (Fst.plus_O_n (|n| * m)).",
        "\n      Compute {| Fst.fst := n; Fst.snd := n |}.",
        "\n      reflexivity.",
        "\n    Qed.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(47, 10),
            [],
            GoalConfig(
                [Goal([], "∀ n m : nat, | n | * m = 0 + | n | * m")], [], [], []
            ),
        ),
        GoalAnswer(
            versionId,
            Position(48, 17),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "| n | * m = 0 + | n | * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(
            versionId,
            Position(49, 42),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "| n | * m = | n | * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(
            versionId,
            Position(50, 47),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "| n | * m = | n | * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(versionId, Position(51, 18), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
        [
            "Theorem plus_O_n : forall n:nat, n = 0 + n.",
            'Notation "x * y" := (Nat.mul x y) : nat_scope',
            'Notation "| a |" := (S a)',
        ],
        ["Record example := mk_example { fst : nat; snd : nat }."],
        [],
        [],
    ]

    for i in range(5):
        assert proof_steps[3][i].text == texts[i]
        assert str(proof_steps[3][i].goals) == str(goals[i])
        assert proof_steps[3][i].context == contexts[i]
