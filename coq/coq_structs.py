import re
from enum import Enum
from typing import Dict, List, Union, Callable
from coq.lsp.coq_lsp_structs import RangedSpan, GoalAnswer
from lsp.lsp_structs import Diagnostic, Position


class SegmentType(Enum):
    MODULE = 1
    MODULE_TYPE = 2
    SECTION = 3


class TermType(Enum):
    THEOREM = 1
    LEMMA = 2
    DEFINITION = 3
    NOTATION = 4
    INDUCTIVE = 5
    COINDUCTIVE = 6
    RECORD = 7
    CLASS = 8
    INSTANCE = 9
    FIXPOINT = 10
    COFIXPOINT = 11
    SCHEME = 12
    VARIANT = 13
    FACT = 14
    REMARK = 15
    COROLLARY = 16
    PROPOSITION = 17
    PROPERTY = 18
    OBLIGATION = 19
    TACTIC = 20
    RELATION = 21
    SETOID = 22
    FUNCTION = 23
    DERIVE = 24
    OTHER = 100


class CoqErrorCodes(Enum):
    InvalidFile = 0
    NotationNotFound = 1


class CoqError(Exception):
    def __init__(self, code: CoqErrorCodes, message: str):
        self.code = code
        self.message = message


class Step(object):
    def __init__(self, text: str, short_text: str, ast: RangedSpan):
        self.text = text
        self.short_text = short_text
        self.ast = ast
        self.diagnostics: List[Diagnostic] = []


class Term:
    def __init__(
        self,
        step: Step,
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
        self.step = step
        self.type = term_type
        self.file_path = file_path
        self.module = module

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Term):
            return False
        return __value.text == self.text

    def __hash__(self) -> int:
        return hash(self.text)

    @property
    def text(self) -> str:
        return self.step.short_text

    @property
    def ast(self) -> RangedSpan:
        return self.step.ast


class ProofStep:
    def __init__(
        self,
        step: Step,
        goals: Union[GoalAnswer, Callable[[Position], GoalAnswer]],
        context: List[Term],
    ):
        self.step = step
        self._goals = goals
        self.context = context

    @property
    def goals(self) -> GoalAnswer:
        if callable(self._goals):
            self._goals = self._goals(self.ast.range.start)
        return self._goals

    @goals.setter
    def goals(self, goals: Union[GoalAnswer, Callable[[Position], GoalAnswer]]):
        self._goals = goals

    @property
    def ast(self) -> RangedSpan:
        return self.step.ast

    @property
    def text(self) -> str:
        return self.step.text

    @property
    def diagnostics(self) -> List[Diagnostic]:
        return self.step.diagnostics


class ProofTerm(Term):
    def __init__(self, term: Term, context: List[Term], steps: List[ProofStep]):
        super().__init__(term.step, term.type, term.file_path, term.module)
        self.steps = steps
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
            notation (str): Id of the notation. E.g. "_ + _"
            scope (str): Scope of the notation. E.g. "nat_scope"

        Raises:
            RuntimeError: If the notation is not found in the context.

        Returns:
            Term: Term that corresponds to the notation.
        """
        notation_id = FileContext.get_notation_key(notation, scope)
        regex = f"{re.escape(notation_id)}".split("\\ ")
        for i, sub in enumerate(regex):
            if sub == "_":
                # We match the wildcard with the description from here:
                # https://coq.inria.fr/distrib/current/refman/language/core/basic.html#grammar-token-ident
                # Coq accepts more characters, but no one should need more than these...
                chars = "A-Za-zÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙա-և"
                regex[i] = f"([{chars}][{chars}0-9_']*|_[{chars}0-9_']+)"
            else:
                # Handle '_'
                regex[i] = f"({sub}|('{sub}'))"
        regex = "^" + "\\ ".join(regex) + "$"

        # Search notations
        unscoped = None
        for term in self.terms.keys():
            if re.match(regex, term):
                return self.terms[term]
            if re.match(regex, term.split(":")[0].strip()):
                unscoped = term
        # In case the stored id contains the scope but no scope is provided
        if unscoped is not None:
            return self.terms[unscoped]

        # Search Infix
        if re.match("^_ ([^ ]*) _$", notation):
            op = notation[2:-2]
            key = FileContext.get_notation_key(op, scope)
            if key in self.terms:
                return self.terms[key]

        raise CoqError(
            CoqErrorCodes.NotationNotFound,
            f"Notation not found in context: {notation_id}",
        )

    @staticmethod
    def get_notation_key(notation: str, scope: str):
        if scope != "" and scope is not None:
            notation += " : " + scope
        return notation
