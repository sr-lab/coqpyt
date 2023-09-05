import os
import subprocess
import pytest
from typing import List, Tuple
from coqlspclient.coq_lsp_structs import *
from coqlspclient.coq_structs import TermType, Term
from coqlspclient.proof_state import ProofState, CoqFile

versionId: VersionedTextDocumentIdentifier = None
state: ProofState = None
workspace: str = None


def compare_context(
    test_context: List[Tuple[str, TermType, List[str]]], context: List[Term]
):
    assert len(test_context) == len(context)
    for i in range(len(context)):
        assert test_context[i][0] == context[i].text
        assert test_context[i][1] == context[i].type
        assert test_context[i][2] == context[i].module


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
        "\n      intros n.",
        "\n      Print plus.",
        "\n      Print Nat.add.",
        "\n      reduce_eq.",
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
    ]
    contexts = [
        [],
        [("Notation plus := Nat.add (only parsing).", TermType.NOTATION, [])],
        [
            (
                'Fixpoint add n m := match n with | 0 => m | S p => S (p + m) end where "n + m" := (add n m) : nat_scope.',
                TermType.FIXPOINT,
                [],
            )
        ],
        [("Ltac reduce_eq := simpl; reflexivity.", TermType.TACTIC, [])],
    ]
    statement_context = [
        ("Inductive nat : Set := | O : nat | S : nat -> nat.", TermType.INDUCTIVE, []),
        ('Notation "x = y :> A" := (@eq A x y) : type_scope', TermType.NOTATION, []),
        ('Notation "n + m" := (add n m) : nat_scope', TermType.NOTATION, []),
    ]

    compare_context(statement_context, proofs[0].context)
    assert proofs[0].text == "Theorem plus_O_n : forall n:nat, 0 + n = n."
    for i in range(4):
        assert proofs[0].steps[i].text == texts[i]
        assert str(proofs[0].steps[i].goals) == str(goals[i])
        compare_context(contexts[i], proofs[0].steps[i].context)

    texts = [
        "\n    intros n m.",
        "\n    rewrite -> (plus_O_n (S n * m)).",
        "\n    Compute True /\\ True.",
        "\n    reflexivity.",
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
    ]
    contexts = [
        [],
        [
            ("Lemma plus_O_n : forall n:nat, 0 + n = n.", TermType.LEMMA, []),
            ('Notation "n * m" := (mul n m) : nat_scope', TermType.NOTATION, []),
            (
                "Inductive nat : Set := | O : nat | S : nat -> nat.",
                TermType.INDUCTIVE,
                [],
            ),
        ],
        [
            ('Notation "A /\\ B" := (and A B) : type_scope', TermType.NOTATION, []),
            ("Inductive True : Prop := I : True.", TermType.INDUCTIVE, []),
        ],
        [],
    ]
    ranges = [
        (22, 4, 22, 15),
        (23, 4, 23, 36),
        (24, 4, 24, 25),
        (25, 4, 25, 16),
    ]
    statement_context = [
        (
            "Notation \"∀ x .. y , P\" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity, format \"'[ ' '[ ' ∀ x .. y ']' , "
            + "'/' P ']'\") : type_scope.",
            TermType.NOTATION,
            [],
        ),
        ('Notation "x = y :> A" := (@eq A x y) : type_scope', TermType.NOTATION, []),
        ('Notation "n + m" := (add n m) : nat_scope', TermType.NOTATION, []),
        ('Notation "n * m" := (mul n m) : nat_scope', TermType.NOTATION, []),
        ("Inductive nat : Set := | O : nat | S : nat -> nat.", TermType.INDUCTIVE, []),
    ]

    compare_context(statement_context, proofs[1].context)
    assert (
        proofs[1].text
        == "Definition mult_0_plus : ∀ n m : nat, 0 + (S n * m) = S n * m."
    )
    for i in range(4):
        assert proofs[1].steps[i].ast.range.start.line == ranges[i][0]
        assert proofs[1].steps[i].ast.range.start.character == ranges[i][1]
        assert proofs[1].steps[i].ast.range.end.line == ranges[i][2]
        assert proofs[1].steps[i].ast.range.end.character == ranges[i][3]
        assert proofs[1].steps[i].text == texts[i]
        assert str(proofs[1].steps[i].goals) == str(goals[i])
        compare_context(contexts[i], proofs[1].steps[i].context)

    texts = [
        "\n      intros n.",
        "\n      Compute mk_example n n.",
        "\n      Compute Out.In.plus_O_n.",
        "\n      reduce_eq.",
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
    ]
    contexts = [
        [],
        [
            (
                "Record example := mk_example { fst : nat; snd : nat }.",
                TermType.RECORD,
                ["Extra", "Fst"],
            )
        ],
        [
            (
                "Theorem plus_O_n : forall n:nat, 0 + n = n.",
                TermType.THEOREM,
                ["Out", "In"],
            )
        ],
        [("Ltac reduce_eq := simpl; reflexivity.", TermType.TACTIC, [])],
    ]
    statement_context = [
        ("Inductive nat : Set := | O : nat | S : nat -> nat.", TermType.INDUCTIVE, []),
        ('Notation "x = y :> A" := (@eq A x y) : type_scope', TermType.NOTATION, []),
        ('Notation "n + m" := (add n m) : nat_scope', TermType.NOTATION, []),
    ]

    compare_context(statement_context, proofs[2].context)
    assert proofs[2].text == "Theorem plus_O_n : forall n:nat, n = 0 + n."
    for i in range(4):
        assert proofs[2].steps[i].text == texts[i]
        assert str(proofs[2].steps[i].goals) == str(goals[i])
        compare_context(contexts[i], proofs[2].steps[i].context)

    texts = [
        "\n      intros n m.",
        "\n      rewrite <- (Fst.plus_O_n (|n| * m)).",
        "\n      Compute {| Fst.fst := n; Fst.snd := n |}.",
        "\n      reflexivity.",
    ]
    goals = [
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
    ]
    contexts = [
        [],
        [
            (
                "Theorem plus_O_n : forall n:nat, n = 0 + n.",
                TermType.THEOREM,
                ["Extra", "Fst"],
            ),
            ('Notation "n * m" := (mul n m) : nat_scope', TermType.NOTATION, []),
            (
                'Notation "| a |" := (S a) (at level 30, right associativity).',
                TermType.NOTATION,
                ["Extra", "Snd"],
            ),
        ],
        [
            (
                "Record example := mk_example { fst : nat; snd : nat }.",
                TermType.RECORD,
                ["Extra", "Fst"],
            )
        ],
        [],
    ]
    statement_context = [
        (
            "Notation \"∀ x .. y , P\" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity, format \"'[ ' '[ ' ∀ x .. y ']' , "
            + "'/' P ']'\") : type_scope.",
            TermType.NOTATION,
            [],
        ),
        ('Notation "x = y :> A" := (@eq A x y) : type_scope', TermType.NOTATION, []),
        ('Notation "n * m" := (mul n m) : nat_scope', TermType.NOTATION, []),
        ("Inductive nat : Set := | O : nat | S : nat -> nat.", TermType.INDUCTIVE, []),
        ('Notation "n + m" := (add n m) : nat_scope', TermType.NOTATION, []),
    ]

    compare_context(statement_context, proofs[3].context)
    assert (
        proofs[3].text == "Theorem mult_0_plus : ∀ n m : nat, S n * m = 0 + (S n * m)."
    )
    for i in range(4):
        assert proofs[3].steps[i].text == texts[i]
        assert str(proofs[3].steps[i].goals) == str(goals[i])
        compare_context(contexts[i], proofs[3].steps[i].context)


@pytest.mark.parametrize(
    "setup", [("test_imports/test_import.v", "test_imports/")], indirect=True
)
def test_imports(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 2
    context = [
        [],
        [
            ("Local Theorem plus_O_n : forall n:nat, 0 + n = n.", TermType.THEOREM, []),
            ('Notation "n * m" := (mul n m) : nat_scope', TermType.NOTATION, []),
            (
                "Inductive nat : Set := | O : nat | S : nat -> nat.",
                TermType.INDUCTIVE,
                [],
            ),
        ],
        [],  # FIXME: in the future we should get a Local Theorem from other file here
        [("Lemma plus_O_n : forall n:nat, 0 + n = n.", TermType.LEMMA, [])],
        [],
    ]

    assert len(proofs[1].steps) == len(context)
    for i, step in enumerate(proofs[1].steps):
        compare_context(context[i], step.context)


@pytest.mark.parametrize("setup", [("test_non_ending_proof.v", None)], indirect=True)
def test_non_ending_proof(setup, teardown):
    assert len(state.proofs) == 0


@pytest.mark.parametrize("setup", [("test_exists_notation.v", None)], indirect=True)
def test_exists_notation(setup, teardown):
    """Checks if the exists notation is handled. The exists notation is defined
    with 'exists', but the search can be done without the '.
    """
    assert (
        state.context.get_notation("exists _ .. _ , _", "type_scope").text
        == "Notation \"'exists' x .. y , p\" := (ex (fun x => .. (ex (fun y => p)) ..)) (at level 200, x binder, right associativity, format \"'[' 'exists' '/ ' x .. y , '/ ' p ']'\") : type_scope."
    )


@pytest.mark.parametrize("setup", [("test_unknown_notation.v", None)], indirect=True)
def test_unknown_notation(setup, teardown):
    """Checks if it is able to handle the notation { _ } that is unknown for the
    Locate command because it is a default notation.
    """
    with pytest.raises(RuntimeError):
        assert state.context.get_notation("{ _ }", "")


@pytest.mark.parametrize("setup", [("test_nested_proofs.v", None)], indirect=True)
def test_nested_proofs(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 4

    steps = ["\n    intros n.", "\n    simpl; reflexivity."]
    assert len(proofs[0].steps) == 2
    for i, step in enumerate(proofs[0].steps):
        assert step.text == steps[i]

    steps = [
        "\nintros n m.",
        "\n\nrewrite <- (plus_O_n ((S n) * m)).",
        "\nreflexivity.",
    ]
    assert len(proofs[1].steps) == 3
    for i, step in enumerate(proofs[1].steps):
        assert step.text == steps[i]

    steps = [
        "\n    intros n.",
        "\n    simpl; reflexivity.",
    ]
    assert len(proofs[2].steps) == 2
    for i, step in enumerate(proofs[2].steps):
        assert step.text == steps[i]

    steps = [
        "\n    intros n.",
        "\n    simpl; reflexivity.",
    ]
    assert len(proofs[3].steps) == 2
    for i, step in enumerate(proofs[3].steps):
        assert step.text == steps[i]


@pytest.mark.parametrize("setup", [("test_theorem_tokens.v", None)], indirect=True)
def test_theorem_tokens(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 7
    assert proofs[0].type == TermType.REMARK
    assert proofs[1].type == TermType.FACT
    assert proofs[2].type == TermType.COROLLARY
    assert proofs[3].type == TermType.PROPOSITION
    assert proofs[4].type == TermType.PROPERTY
    assert proofs[5].type == TermType.THEOREM
    assert proofs[6].type == TermType.LEMMA


@pytest.mark.parametrize("setup", [("test_bullets.v", None)], indirect=True)
def test_bullets(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 1
    steps = [
        "\n    intros x y. ",
        " split.",
        "\n    - ",
        " reflexivity.",
        "\n    - ",
        " reflexivity.",
    ]
    assert len(proofs[0].steps) == 6
    for i, step in enumerate(proofs[0].steps):
        assert step.text == steps[i]


@pytest.mark.parametrize("setup", [("test_obligation.v", None)], indirect=True)
def test_obligation(setup, teardown):
    proofs = state.proofs
    assert len(proofs) == 11

    statement_context = [
        ("Inductive nat : Set := | O : nat | S : nat -> nat.", TermType.INDUCTIVE, []),
        ("Notation dec := sumbool_of_bool.", TermType.NOTATION, []),
        ("Notation leb := Nat.leb (only parsing).", TermType.NOTATION, []),
        ("Notation pred := Nat.pred (only parsing).", TermType.NOTATION, []),
        (
            'Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) : type_scope.',
            TermType.NOTATION,
            [],
        ),
        ('Notation "x = y :> A" := (@eq A x y) : type_scope', TermType.NOTATION, []),
    ]
    programs = [
        ("id1", "S (pred n)"),
        ("id1", "S (pred n)"),
        ("id2", "S (pred n)"),
        ("id2", "S (pred n)"),
        ("id3", "S (pred n)"),
        ("id3", "S (pred n)"),
        ("id4", "S (pred n)"),
        ("id4", "S (pred n)"),
        ("id", "pred (S n)"),
        ("id", "S (pred n)"),
        ("id", "S (pred n)"),
    ]

    for i, proof in enumerate(proofs):
        compare_context(statement_context, proof.context)
        assert (
            proof.text
            == "Program Definition "
            + programs[i][0]
            + " (n : nat) : { x : nat | x = n } := if dec (leb n 0) then 0%nat else "
            + programs[i][1]
            + "."
        )
        assert len(proof.steps) == 1
        assert proof.steps[0].text == "\n  dummy_tactic n e."


@pytest.mark.parametrize("setup", [("test_module_type.v", None)], indirect=True)
def test_module_type(setup, teardown):
    # We ignore proofs inside a Module Type since they can't be used outside
    # and should be overriden.
    assert len(state.proofs) == 1


@pytest.mark.parametrize("setup", [("test_type_class.v", None)], indirect=True)
def test_type_class(setup, teardown):
    assert len(state.proofs) == 2
    assert len(state.proofs[0].steps) == 2
    assert (
        state.proofs[0].text
        == "#[refine] Global Instance unit_EqDec : TypeClass.EqDecNew unit := { eqb_new x y := true }."
    )

    context = [
        (
            "Class EqDecNew (A : Type) := { eqb_new : A -> A -> bool ; eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ; eqb_ident_new : forall x, eqb_new x x = true }.",
            TermType.CLASS,
            ["TypeClass"],
        ),
        ("Inductive unit : Set := tt : unit.", TermType.INDUCTIVE, []),
        (
            "Inductive bool : Set := | true : bool | false : bool.",
            TermType.INDUCTIVE,
            [],
        ),
    ]
    compare_context(context, state.proofs[0].context)

    assert (
        state.proofs[1].text
        == "Instance test : TypeClass.EqDecNew unit -> TypeClass.EqDecNew unit."
    )

    context = [
        (
            'Notation "A -> B" := (forall (_ : A), B) : type_scope.',
            TermType.NOTATION,
            [],
        ),
        (
            "Class EqDecNew (A : Type) := { eqb_new : A -> A -> bool ; eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ; eqb_ident_new : forall x, eqb_new x x = true }.",
            TermType.CLASS,
            ["TypeClass"],
        ),
        ("Inductive unit : Set := tt : unit.", TermType.INDUCTIVE, []),
    ]
    compare_context(context, state.proofs[1].context)
