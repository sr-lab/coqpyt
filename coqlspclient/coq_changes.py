from dataclasses import dataclass


class CoqChange:
    pass


@dataclass
class CoqAddStep(CoqChange):
    step_text: str
    previous_step_index: int


@dataclass
class CoqDeleteStep(CoqChange):
    step_index: int
