from dataclasses import dataclass


class CoqChange:
    pass


@dataclass
class CoqAdd(CoqChange):
    step_text: str
    previous_step_index: int


@dataclass
class CoqDelete(CoqChange):
    step_index: int


class ProofChange:
    pass


@dataclass
class ProofAppend(ProofChange):
    step_text: str


@dataclass
class ProofPop(ProofChange):
    pass
