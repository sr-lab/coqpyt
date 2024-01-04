from coqpyt.coq.context import FileContext
from coqpyt.coq.structs import Term, TermType, Step


def test_notation_colon_problem():
    context = FileContext("tests/tests.v")
    mock_context = {
        "x : y : type_scope": Term(
            Step("XXX", "YYY", None), TermType.NOTATION, "tests/tests.v", []
        )
    }
    context.update(mock_context)
    term = context.get_notation("_ : _", "")
    assert term == mock_context["x : y : type_scope"]


def test_notation_unscoped():
    context = FileContext("tests/tests.v")
    mock_context = {
        "x : y": Term(
            Step("XXX", "YYY", None), TermType.NOTATION, "tests/tests.v", []
        ),
        "z : y : test_scope": Term(
            Step("ZZZ", "WWW", None), TermType.NOTATION, "tests/tests.v", []
        )
    }
    context.update(mock_context)

    term = context.get_notation("_ : _", "type_scope")
    assert term == mock_context["x : y"]

    term = context.get_notation("_ : _", "")
    assert term == mock_context["x : y"]

    term = context.get_notation("_ : _", "test_scope")
    assert term == mock_context["z : y : test_scope"]