import os
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


@pytest.mark.parametrize("setup", ["test_invalid_2.v"], indirect=True)
def test_is_invalid_2(setup, teardown):
    assert not coq_file.is_valid


@pytest.mark.parametrize("setup", ["test_module_type.v"], indirect=True)
def test_module_type(setup, teardown):
    coq_file.run()
    # We ignore terms inside a Module Type since they can't be used outside
    # and should be overriden.
    assert len(coq_file.context.terms) == 1
