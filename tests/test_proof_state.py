import os
import subprocess
import pytest
from coqlspclient.coq_lsp_structs import *
from coqlspclient.coq_structs import Term
from coqlspclient.proof_state import ProofState, CoqFile

versionId: VersionedTextDocumentIdentifier = None
state: ProofState = None
workspace: str = None


def get_context_texts(context: List[Term]):
    return list(map(lambda term: term.text, context))


@pytest.fixture
def setup(request):
    global state, versionId, workspace
    file_path, workspace = request.param[0], request.param[1]
    file_path = os.path.join("tests/resources", file_path)
    if workspace is not None:
        workspace = os.path.join(os.getcwd(), "tests/resources", workspace)
        subprocess.run(f"cd {workspace} && make", shell=True, capture_output=True)
    uri = "file://" + file_path
    state = ProofState(CoqFile(file_path, timeout=60, workspace=workspace))
    versionId = VersionedTextDocumentIdentifier(uri, 1)
    yield


@pytest.fixture
def teardown(request):
    yield
    if workspace is not None:
        subprocess.run(f"cd {workspace} && make clean", shell=True, capture_output=True)
    state.close()


@pytest.mark.parametrize("setup", [("test_valid.v", None)], indirect=True)
def test_get_proofs(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 4

    texts = [
        "\n    Proof.",
        "\n      intros n.",
        "\n      Print plus.",
        "\n      Print Nat.add.",
        "\n      reduce_eq.",
        "\n    Qed.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(8, 47),
            [],
            GoalConfig([Goal([], "∀ n : nat, 0 + n = n")], [], [], []),
        ),
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
        [],
        ["Notation plus := Nat.add (only parsing)."],
        [
            'Fixpoint add n m := match n with | 0 => m | S p => S (p + m) end where "n + m" := (add n m) : nat_scope.'
        ],
        ["Ltac reduce_eq := simpl; reflexivity."],
        [],
    ]

    for i in range(6):
        assert proofs[0][i].text == texts[i]
        assert str(proofs[0][i].goals) == str(goals[i])
        assert get_context_texts(proofs[0][i].context) == contexts[i]

    texts = [
        "\n  Proof.",
        "\n    intros n m.",
        "\n    rewrite -> (plus_O_n (S n * m)).",
        "\n    Compute True /\\ True.",
        "\n    reflexivity.",
        "\n  Defined.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(20, 28),
            [],
            GoalConfig([Goal([], "∀ n m : nat, 0 + S n * m = S n * m")], [], [], []),
        ),
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
    ranges = [
        (21, 2, 21, 8),
        (22, 4, 22, 15),
        (23, 4, 23, 36),
        (24, 4, 24, 25),
        (25, 4, 25, 16),
        (26, 2, 26, 10),
    ]

    for i in range(6):
        assert proofs[1][i].ast.range.start.line == ranges[i][0]
        assert proofs[1][i].ast.range.start.character == ranges[i][1]
        assert proofs[1][i].ast.range.end.line == ranges[i][2]
        assert proofs[1][i].ast.range.end.character == ranges[i][3]
        assert proofs[1][i].text == texts[i]
        assert str(proofs[1][i].goals) == str(goals[i])
        assert get_context_texts(proofs[1][i].context) == contexts[i]

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
            Position(33, 47),
            [],
            GoalConfig([Goal([], "∀ n : nat, n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(34, 15),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(35, 29),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(
            versionId,
            Position(36, 30),
            [],
            GoalConfig([Goal([Hyp(["n"], "nat", None)], "n = 0 + n")], [], [], []),
        ),
        GoalAnswer(versionId, Position(37, 16), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
        ["Record example := mk_example { fst : nat; snd : nat }."],
        ["Theorem plus_O_n : forall n:nat, 0 + n = n."],
        ["Ltac reduce_eq := simpl; reflexivity."],
        [],
    ]

    for i in range(5):
        assert proofs[2][i].text == texts[i]
        assert str(proofs[2][i].goals) == str(goals[i])
        assert get_context_texts(proofs[2][i].context) == contexts[i]

    texts = [
        "\n    Proof.",
        "\n      intros n m.",
        "\n      rewrite <- (Fst.plus_O_n (|n| * m)).",
        "\n      Compute {| Fst.fst := n; Fst.snd := n |}.",
        "\n      reflexivity.",
        "\n    Admitted.",
    ]
    goals = [
        GoalAnswer(
            versionId,
            Position(45, 30),
            [],
            GoalConfig(
                [Goal([], "∀ n m : nat, | n | * m = 0 + | n | * m")], [], [], []
            ),
        ),
        GoalAnswer(
            versionId,
            Position(46, 10),
            [],
            GoalConfig(
                [Goal([], "∀ n m : nat, | n | * m = 0 + | n | * m")], [], [], []
            ),
        ),
        GoalAnswer(
            versionId,
            Position(47, 17),
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
            Position(48, 42),
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
            Position(49, 47),
            [],
            GoalConfig(
                [Goal([Hyp(["n", "m"], "nat", None)], "| n | * m = | n | * m")],
                [],
                [],
                [],
            ),
        ),
        GoalAnswer(versionId, Position(50, 18), [], GoalConfig([], [], [], [])),
    ]
    contexts = [
        [],
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

    for i in range(6):
        assert proofs[3][i].text == texts[i]
        assert str(proofs[3][i].goals) == str(goals[i])
        assert get_context_texts(proofs[3][i].context) == contexts[i]


@pytest.mark.parametrize(
    "setup", [("test_imports/test_import.v", "test_imports/")], indirect=True
)
def test_imports(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 2
    context = [
        [],
        [],
        [
            "Local Theorem plus_O_n : forall n:nat, 0 + n = n.",
            'Notation "x * y" := (Nat.mul x y) : nat_scope',
            "Inductive nat : Set := | O : nat | S : nat -> nat.",
        ],
        [],  # FIXME: in the future we should get a Local Theorem from other file here
        ["Lemma plus_O_n : forall n:nat, 0 + n = n."],
        [],
        [],
    ]

    assert len(proofs[1]) == len(context)
    for i, step in enumerate(proofs[1]):
        assert get_context_texts(step.context) == context[i]
