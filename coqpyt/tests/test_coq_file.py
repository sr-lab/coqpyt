import os
import uuid
import shutil
import pytest
import tempfile

from coqpyt.coq.exceptions import *
from coqpyt.coq.changes import *
from coqpyt.coq.base_file import CoqFile

coq_file: CoqFile = None


@pytest.fixture
def setup(request):
    global coq_file
    file_path = os.path.join("tests/resources", request.param)
    new_file_path = os.path.join(
        tempfile.gettempdir(),
        "test" + str(uuid.uuid4()).replace("-", "") + ".v",
    )
    shutil.copyfile(file_path, new_file_path)
    coq_file = CoqFile(new_file_path, timeout=60)
    yield


@pytest.fixture
def teardown():
    yield
    coq_file.close()
    os.remove(coq_file.path)


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_is_valid(setup, teardown):
    assert coq_file.is_valid


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_negative_step(setup, teardown):
    steps = coq_file.exec(nsteps=8)
    assert steps[-1].text == "\n      Print plus."
    steps = coq_file.exec(nsteps=-1)
    assert steps[0].text == "\n      Print plus."

    assert "Out.In.plus_O_n" in coq_file.context.terms
    steps = coq_file.exec(nsteps=-3)
    assert steps[0].text == "\n    Theorem plus_O_n : forall n:nat, 0 + n = n."
    assert "Out.In.plus_O_n" not in coq_file.context.terms

    assert coq_file.context.curr_modules == ["Out", "In"]
    steps = coq_file.exec(nsteps=-1)
    assert steps[0].text == "\n  Module In."
    assert coq_file.context.curr_modules == ["Out"]


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_delete_step(setup, teardown):
    assert coq_file.steps[8].text == "\n      Print Nat.add."
    assert coq_file.steps[8].ast.range.start.line == 12

    steps = coq_file.exec(nsteps=10)
    assert steps[-1].text == "\n      reduce_eq."

    coq_file.delete_step(7)
    assert coq_file.steps[7].text == "\n      Print Nat.add."
    assert coq_file.steps[7].ast.range.start.line == 11

    steps = coq_file.exec(nsteps=1)
    assert steps[-1].text == "\n    Qed."

    with open(coq_file.path, "r") as f:
        assert "Print plus." not in f.read()


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_add_step(setup, teardown):
    assert coq_file.steps[8].text == "\n      Print Nat.add."
    assert coq_file.steps[8].ast.range.start.line == 12

    steps = coq_file.exec(nsteps=8)
    assert steps[-1].text == "\n      Print plus."
    steps_taken = coq_file.steps_taken

    coq_file.add_step(7, "\n      Print minus.")
    assert coq_file.steps_taken == steps_taken
    steps = coq_file.exec(nsteps=1)
    steps_taken = coq_file.steps_taken
    assert steps[-1].text == "\n      Print minus."

    coq_file.add_step(6, "\n      Print minus.")
    assert coq_file.steps_taken == steps_taken + 1
    steps = coq_file.exec(nsteps=1)
    assert steps[-1].text == "\n      Print Nat.add."
    assert steps[-1].ast.range.start.line == 14


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_add_definition(setup, teardown):
    coq_file.exec(5)
    steps_taken = coq_file.steps_taken

    assert "x" not in coq_file.context.terms
    coq_file.add_step(0, "\nDefinition x := 0.")
    assert "x" in coq_file.context.terms
    assert coq_file.context.get_term("x").text == "Definition x := 0."
    assert coq_file.steps_taken == steps_taken + 1


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_change_steps(setup, teardown):
    assert coq_file.steps[8].text == "\n      Print Nat.add."
    assert coq_file.steps[8].ast.range.start.line == 12

    changes = [
        CoqAddStep("\n      Print minus.", 7),
        CoqAddStep("\n      Print minus.", 6),
        CoqDeleteStep(9),  # Delete first print minus
        CoqDeleteStep(19),  # Delete Compute True /\ True.
    ]
    coq_file.change_steps(changes)
    steps = coq_file.exec(nsteps=8)
    assert steps[-1].text == "\n      Print minus."
    assert steps[-1].ast.range.start.line == 11
    steps = coq_file.exec(nsteps=1)
    assert steps[-1].text == "\n      Print plus."
    assert coq_file.steps[8].ast.range.start.line == 12
    steps = coq_file.exec(nsteps=11)
    assert steps[-1].text == "\n    reflexivity."

    with pytest.raises(InvalidChangeException):
        coq_file.change_steps(
            [
                CoqAddStep("\n      Print minus.", 7),
                CoqDeleteStep(11),  # delete reduce_eq
            ]
        )


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_add_proof(setup, teardown):
    coq_file.run()
    steps_taken = coq_file.steps_taken
    assert "change_steps" not in coq_file.context.terms

    coq_file.change_steps(
        [
            CoqAddStep(" Defined.", 12),
            CoqAddStep("\n  reflexivity.", 12),
            CoqAddStep("\n  rewrite -> (plus_O_n (S n * m)).", 12),
            # Checks if there aren't problems with intermediate states
            # (e.g. the ranges of the AST are updated incorrectly)
            CoqDeleteStep(13),
            CoqAddStep("\n  intros n m.", 12),
            CoqAddStep("\nProof.", 12),
            CoqAddStep(
                "\nDefinition change_steps :  ∀ n m : nat,\n 0 + (S n * m) = S n * m.",
                12,
            ),
        ]
    )

    assert "change_steps" in coq_file.context.terms
    assert coq_file.steps_taken == steps_taken + 5


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_delete_proof(setup, teardown):
    # Test if mult_0_plus is removed
    # It also tests if deletion with invalid intermediate states works
    coq_file.run()
    steps_taken = coq_file.steps_taken
    assert "mult_0_plus" in coq_file.context.terms
    coq_file.change_steps([CoqDeleteStep(14) for _ in range(7)])
    assert "mult_0_plus" not in coq_file.context.terms
    assert coq_file.steps_taken == steps_taken - 7


@pytest.mark.parametrize("setup", ["test_where_notation.v"], indirect=True)
def test_where_notation(setup, teardown):
    coq_file.run()
    assert "n + m : test_scope" in coq_file.context.terms
    assert (
        coq_file.context.terms["n + m : test_scope"].text
        == 'Fixpoint plus_test (n m : nat) {struct n} : nat := match n with | O => m | S p => S (p + m) end where "n + m" := (plus n m) : test_scope and "n - m" := (minus n m).'
    )
    assert "n - m" in coq_file.context.terms
    assert (
        coq_file.context.terms["n - m"].text
        == 'Fixpoint plus_test (n m : nat) {struct n} : nat := match n with | O => m | S p => S (p + m) end where "n + m" := (plus n m) : test_scope and "n - m" := (minus n m).'
    )
    assert "A & B" in coq_file.context.terms
    assert (
        coq_file.context.terms["A & B"].text
        == "Inductive and' (A B : Prop) : Prop := conj' : A -> B -> A & B where \"A & B\" := (and' A B)."
    )
    assert "'ONE'" in coq_file.context.terms
    assert (
        coq_file.context.terms["'ONE'"].text
        == "Fixpoint incr (n : nat) : nat := n + ONE where \"'ONE'\" := 1."
    )
    assert "x 🀄 y" in coq_file.context.terms
    assert (
        coq_file.context.terms["x 🀄 y"].text
        == 'Fixpoint unicode x y := x 🀄 y where "x 🀄 y" := (plus_test x y).'
    )


@pytest.mark.parametrize("setup", ["test_get_notation.v"], indirect=True)
def test_get_notation(setup, teardown):
    coq_file.run()
    assert (
        coq_file.context.get_notation("'_' _ '_' _ '_'", "test_scope").text
        == "Notation \"'_' AB '_' BC '_'\" := (plus AB BC) : test_scope."
    )
    assert (
        coq_file.context.get_notation("'C_D' _ 'C_D'", "test_scope").text
        == "Notation \"'C_D' A_B 'C_D'\" := (plus A_B A_B) : test_scope."
    )
    assert (
        coq_file.context.get_notation("_ ++ _", "list_scope").text
        == 'Infix "++" := app (right associativity, at level 60) : list_scope.'
    )


@pytest.mark.parametrize("setup", ["test_invalid_1.v"], indirect=True)
def test_is_invalid_1(setup, teardown):
    assert not coq_file.is_valid
    steps = coq_file.run()
    assert len(steps[11].diagnostics) == 1
    assert (
        steps[11].diagnostics[0].message
        == 'Found no subterm matching "0 + ?M152" in the current goal.'
    )
    assert steps[11].diagnostics[0].severity == 1


@pytest.mark.parametrize("setup", ["test_invalid_2.v"], indirect=True)
def test_is_invalid_2(setup, teardown):
    assert not coq_file.is_valid
    steps = coq_file.run()
    assert len(steps[15].diagnostics) == 1
    assert (
        steps[15].diagnostics[0].message
        == "Syntax error: '.' expected after [command] (in [vernac_aux])."
    )
    assert steps[15].diagnostics[0].severity == 1


@pytest.mark.parametrize("setup", ["test_module_type.v"], indirect=True)
def test_module_type(setup, teardown):
    coq_file.run()
    # We ignore terms inside a Module Type since they can't be used outside
    # and should be overriden.
    assert len(coq_file.context.terms) == 1
    assert "plus_O_n" in coq_file.context.terms


@pytest.mark.parametrize("setup", ["test_derive.v"], indirect=True)
def test_derive(setup, teardown):
    coq_file.run()
    for key in ["incr", "incr_correct"]:
        assert key in coq_file.context.terms
        assert (
            coq_file.context.terms[key].text
            == "Derive incr SuchThat (forall n, incr n = plus 1 n) As incr_correct."
        )
    keywords = [
        "Inversion",
        "Inversion_clear",
        "Dependent Inversion",
        "Dependent Inversion_clear",
    ]
    for i in range(4):
        key = f"leminv{i + 1}"
        assert key in coq_file.context.terms
        assert (
            coq_file.context.terms[key].text
            == f"Derive {keywords[i]} {key} with (forall n m:nat, Le (S n) m) Sort Prop."
        )


def test_space_in_path():
    # This test exists because coq-lsp encodes spaces in paths as %20
    # This causes the diagnostics to be saved in a different path than the one
    # considered by CoqPyt. This was fixed by unquoting the path given
    # by coq-lsp.
    with CoqFile("tests/resources/test test/test_error.v") as coq_file:
        assert not coq_file.is_valid
