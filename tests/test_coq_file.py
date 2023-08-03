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


@pytest.mark.parametrize("setup", ["test_invalid_1.v"], indirect=True)
def test_is_invalid_1(setup, teardown):
    assert not coq_file.is_valid


@pytest.mark.parametrize("setup", ["test_invalid_2.v"], indirect=True)
def test_is_invalid_2(setup, teardown):
    assert not coq_file.is_valid
