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


# FIXME: Add module?
class Term:
    def __init__(self, text: str, ast: RangedSpan, term_type: TermType, file_path: str):
        """Term of a Coq file.

        Args:
            text (str): The textual representation of the term.
            ast (RangedSpan): The ast representation of the term.
            term_type (TermType): The type of the term.
            file_path (str): The file where the term is.
        """
        self.text = text
        self.ast = ast
        self.type = term_type
        self.file_path = file_path

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


class FileContext(object):
    def __init__(
        self,
        terms: Dict[str, Term] = {},
    ):
        self.terms = terms

    def update(
        self,
        terms: Dict[str, Term] = {},
    ):
        self.terms.update(terms)
