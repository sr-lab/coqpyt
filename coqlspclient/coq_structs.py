import re
from enum import Enum
from typing import Dict, List
from coqlspclient.coq_lsp_structs import RangedSpan, GoalAnswer


class Step(object):
    def __init__(self, text: str, ast: RangedSpan):
        self.text = text
        self.ast = ast


class TermType(Enum):
    THEOREM = 1
    LEMMA = 2
    DEFINITION = 3
    NOTATION = 4
    INDUCTIVE = 5
    RECORD = 6
    FIXPOINT = 7
    TACTIC = 8
    SCHEME = 9
    VARIANT = 10
    OTHER = 100


class Term:
    def __init__(
        self,
        text: str,
        ast: RangedSpan,
        term_type: TermType,
        file_path: str,
        module: List[str],
    ):
        """Term of a Coq file.

        Args:
            text (str): The textual representation of the term.
            ast (RangedSpan): The ast representation of the term.
            term_type (TermType): The type of the term.
            file_path (str): The file where the term is.
            module (str): The module where the term is.
        """
        self.text = text
        self.ast = ast
        self.type = term_type
        self.file_path = file_path
        self.module = module

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Term):
            return False
        return __value.text == self.text

    def __hash__(self) -> int:
        return hash(self.text)


class ProofStep(Step):
    def __init__(self, step: Step, goals: GoalAnswer, context: List[Term]):
        super().__init__(step.text, step.ast)
        self.goals = goals
        self.context = context


class FileContext:
    def __init__(self, terms: Dict[str, Term] = None):
        self.terms = {} if terms is None else terms

    def update(
        self,
        terms: Dict[str, Term] = {},
    ):
        self.terms.update(terms)

    def get_notation(self, notation: str, scope: str) -> Term:
        """Get a notation from the context.

        Args:
            notation (str): Name of the notation. E.g. "x + y"
            scope (str): Scope of the notation. E.g. "nat_scope"

        Raises:
            RuntimeError: If the notation is not found in the context.

        Returns:
            Term: Term that corresponds to the notation.
        """
        notation_id = FileContext.get_notation_key(notation, scope)
        regex = f"^{re.escape(notation_id).replace('_', '.')}$"
        for term in self.terms.keys():
            if re.match(regex, term):
                return self.terms[term]
        raise RuntimeError(f"Notation not found in context: {notation_id}")

    @staticmethod
    def get_notation_key(notation: str, scope: str):
        if scope != "" and scope is not None:
            notation += " : " + scope
        return notation
