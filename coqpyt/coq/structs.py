from enum import Enum
from typing import Any, Optional, List, Union, Callable

from coqpyt.lsp.structs import Diagnostic, Position
from coqpyt.coq.lsp.structs import RangedSpan, GoalAnswer


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


class SegmentStack:
    def __init__(self):
        self.modules: List[str] = []
        self.module_types: List[str] = []
        self.sections: List[str] = []
        self.stack: List[SegmentType] = []

    def __match_apply(self, type: SegmentType, operation: Callable, *args: Any):
        match type:
            case SegmentType.MODULE:
                operation(self.modules, *args)
            case SegmentType.MODULE_TYPE:
                operation(self.module_types, *args)
            case SegmentType.SECTION:
                operation(self.sections, *args)

    def push(self, name: str, type: SegmentType):
        self.stack.append(type)
        self.__match_apply(type, list.append, name)

    def pop(self):
        if len(self.stack) > 0:
            self.__match_apply(self.stack.pop(), list.pop)


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
    def __init__(
        self,
        term: Term,
        context: List[Term],
        steps: List[ProofStep],
        program: Optional[Term] = None,
    ):
        super().__init__(term.step, term.type, term.file_path, term.module)
        self.steps = steps
        self.context = context
        self.program = program
