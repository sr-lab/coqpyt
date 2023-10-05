import os
import shutil
import pytest
from coqlspclient.coq_file import CoqFile

coq_file: CoqFile = None


@pytest.fixture
def setup(request):
    global coq_file
    file_path = os.path.join("tests/resources", request.param)
    coq_file = CoqFile(file_path, timeout=60)
    yield


@pytest.fixture
def teardown():
    yield
    coq_file.close()


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_is_valid(setup, teardown):
    assert coq_file.is_valid


@pytest.mark.parametrize("setup", ["test_valid.v"], indirect=True)
def test_negative_step(setup, teardown):
    steps = coq_file.exec(nsteps=8)
    assert steps[-1].text == "\n      Print plus."
    steps = coq_file.exec(nsteps=-1)
    assert steps[0].text == "\n      intros n."
    steps = coq_file.exec(nsteps=-2)
    with pytest.raises(NotImplementedError):
        coq_file.exec(nsteps=-1)


def test_delete_step():
    file_path = os.path.join("tests/resources", "test_valid.v")
    new_file_path = os.path.join("tests/resources", "test_valid_delete.v")
    shutil.copyfile(file_path, new_file_path)
    coq_file = CoqFile(new_file_path, timeout=60)

    try:
        coq_file.delete_step(7)
        assert coq_file.steps[7].text == "\n      Print Nat.add."
        with open(new_file_path, "r") as f:
            assert "Print plus." not in f.read()
    finally:
        coq_file.close()
        if os.path.exists(new_file_path):
            os.remove(new_file_path)


def test_add_step():
    file_path = os.path.join("tests/resources", "test_valid.v")
    new_file_path = os.path.join("tests/resources", "test_valid_add.v")
    shutil.copyfile(file_path, new_file_path)
    coq_file = CoqFile(new_file_path, timeout=60)

    try:
        steps = coq_file.exec(nsteps=8)
        assert steps[-1].text == "\n      Print plus."
        coq_file.add_step("\n      Print minus.", 7)
        steps = coq_file.exec(nsteps=1)
        assert steps[-1].text == "\n      Print minus."
        coq_file.add_step("\n      Print minus.", 6)
        steps = coq_file.exec(nsteps=1)
        assert steps[-1].text == "\n      Print Nat.add."
    finally:
        coq_file.close()
        if os.path.exists(new_file_path):
            os.remove(new_file_path)


@pytest.mark.parametrize("setup", ["test_where_notation.v"], indirect=True)
def test_where_notation(setup, teardown):
    coq_file.run()
    assert "n + m : test_scope" in coq_file.context.terms
    assert (
        coq_file.context.terms["n + m : test_scope"].text
        == 'Notation "n + m" := (plus n m) : test_scope'
    )
    assert "n - m" in coq_file.context.terms
    assert coq_file.context.terms["n - m"].text == 'Notation "n - m" := (minus n m)'
    assert "A & B" in coq_file.context.terms
    assert coq_file.context.terms["A & B"].text == 'Notation "A & B" := (and\' A B)'
    assert "'ONE'" in coq_file.context.terms
    assert coq_file.context.terms["'ONE'"].text == "Notation \"'ONE'\" := 1"
    assert "x 🀄 y" in coq_file.context.terms
    assert coq_file.context.terms["x 🀄 y"].text == 'Notation "x 🀄 y" := (plus_test x y)'


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
