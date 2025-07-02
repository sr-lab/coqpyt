from enum import Enum
from typing import Any, Optional, Tuple, List, Dict

from coqpyt.lsp.structs import Range, VersionedTextDocumentIdentifier, Position


class Hyp(object):
    def __init__(self, names: List[str], ty: str, definition: Optional[str] = None):
        self.names = names
        self.ty = ty
        self.definition = definition

    def __repr__(self) -> str:
        return ", ".join(self.names) + f": {self.ty}"


class Goal(object):
    def __init__(self, hyps: List[Hyp], ty: str):
        self.hyps = hyps
        self.ty = ty

    @staticmethod
    def parse(goal: Dict) -> Optional["Goal"]:
        if "hyps" not in goal:
            return None
        for hyp in goal["hyps"]:
            if "def" in hyp:
                hyp["definition"] = hyp["def"]
                hyp.pop("def")
        hyps = [Hyp(**hyp) for hyp in goal["hyps"]]
        ty = None if "ty" not in goal else goal["ty"]
        return Goal(hyps, ty)

    def __repr__(self) -> str:
        hyps = list(map(lambda hyp: repr(hyp), self.hyps))
        if len(hyps) > 0:
            return "\n".join(hyps) + f"\n\n{self.ty}"
        else:
            return self.ty


class GoalConfig(object):
    def __init__(
        self,
        goals: List[Goal],
        stack: List[Tuple[List[Goal], List[Goal]]],
        shelf: List[Goal],
        given_up: List[Goal],
        bullet: Any = None,
    ):
        self.goals = goals
        self.stack = stack
        self.shelf = shelf
        self.given_up = given_up
        self.bullet = bullet

    def __repr__(self) -> str:
        bold = lambda text: "\033[1m\033[93m" + text + "\033[0m"
        if len(self.goals) > 0:
            res = bold("Goals:\n")
            for goal in self.goals:
                res += "\n" + "-" * 50 + "\n" + repr(goal) + "\n" + "-" * 50
        else:
            res = "No more goals."

        if any(map(lambda stack: len(stack[0]) > 0 or len(stack[1]) > 0, self.stack)):
            res += bold("\n\nStack:")
            for stack in self.stack:
                for goal in stack[0] + stack[1]:
                    res += "\n" + "-" * 50 + "\n" + repr(goal) + "\n" + "-" * 50

        if len(self.shelf) > 0:
            res += bold("\n\nShelf:")
            for goal in self.shelf:
                res += "\n" + "-" * 50 + "\n" + repr(goal) + "\n" + "-" * 50

        if len(self.given_up) > 0:
            res += bold("\n\nGiven up:")
            for goal in self.given_up:
                res += "\n" + "-" * 50 + "\n" + repr(goal) + "\n" + "-" * 50

        res += bold("\n\nBullet: ") + repr(self.bullet)
        return res

    @staticmethod
    def parse(goal_config: Dict) -> Optional["GoalConfig"]:
        parse_goals = lambda goals: [Goal.parse(goal) for goal in goals]
        goals = parse_goals(goal_config["goals"])
        stack = [(parse_goals(t[0]), parse_goals(t[1])) for t in goal_config["stack"]]
        bullet = None if "bullet" not in goal_config else goal_config["bullet"]
        shelf = parse_goals(goal_config["shelf"])
        given_up = parse_goals(goal_config["given_up"])
        return GoalConfig(goals, stack, shelf, given_up, bullet=bullet)


class Message(object):
    def __init__(self, level, text, range=None):
        self.level = level
        self.text = text
        self.range = range


class GoalAnswer(object):
    def __init__(
        self,
        textDocument: VersionedTextDocumentIdentifier,
        position: Position,
        messages: List[Message],
        goals: Optional[GoalConfig] = None,
        error: Any = None,
        program: List = [],
        range: Range = None,
    ):
        self.textDocument = textDocument
        self.position = position
        self.messages = messages
        self.goals = goals
        self.error = error
        self.program = program
        self.range = range

    def __repr__(self):
        res = "\n"

        if len(self.messages) > 0:
            res += "Messages:\n"
            for message in self.messages:
                res += f"{message.level}: {message.text}\n"

        if self.goals is not None:
            res += repr(self.goals)

        if self.error is not None:
            res += "\nError: " + repr(self.error)

        return res

    @staticmethod
    def parse(goal_answer) -> Optional["GoalAnswer"]:
        goal_answer["textDocument"] = VersionedTextDocumentIdentifier(
            **goal_answer["textDocument"]
        )
        goal_answer["position"] = Position(
            goal_answer["position"]["line"], goal_answer["position"]["character"]
        )

        if "goals" in goal_answer:
            goal_answer["goals"] = GoalConfig.parse(goal_answer["goals"])

        for i, message in enumerate(goal_answer["messages"]):
            if not isinstance(message, str):
                if message["range"]:
                    message["range"] = Range(**message["range"])
                goal_answer["messages"][i] = Message(**message)

        return GoalAnswer(**goal_answer)


class Result(object):
    def __init__(self, range, message):
        self.range = range
        self.message = message


class Query(object):
    def __init__(self, query, results):
        self.query = query
        self.results = results


class RangedSpan(object):
    def __init__(self, range: Range, span: Any):
        self.range = range
        self.span = span


class CompletionStatus(object):
    def __init__(self, status: str, range: Range):
        self.status = status
        self.range = range


class FlecheDocument(object):
    def __init__(self, spans: List[RangedSpan], completed: CompletionStatus):
        self.spans = spans
        self.completed = completed

    @staticmethod
    def parse(fleche_document: Dict) -> Optional["FlecheDocument"]:
        if "spans" not in fleche_document or "completed" not in fleche_document:
            return None
        spans: List[RangedSpan] = []
        for span in fleche_document["spans"]:
            range = Range(**span["range"])
            spans.append(
                RangedSpan(range, None if "span" not in span else span["span"])
            )
        completion_status = CompletionStatus(
            fleche_document["completed"]["status"],
            Range(**fleche_document["completed"]["range"]),
        )
        return FlecheDocument(spans, completion_status)


class CoqFileProgressKind(Enum):
    Processing = 1
    FatalError = 2


class CoqFileProgressProcessingInfo(object):
    def __init__(self, range: Range, kind: Optional[CoqFileProgressKind]):
        self.range = range
        self.kind = kind


class CoqFileProgressParams(object):
    def __init__(
        self,
        textDocument: VersionedTextDocumentIdentifier,
        processing: List[CoqFileProgressProcessingInfo],
    ):
        self.textDocument = textDocument
        self.processing = processing

    @staticmethod
    def parse(coqFileProgressParams: Dict) -> Optional["CoqFileProgressParams"]:
        if (
            "textDocument" not in coqFileProgressParams
            or "processing" not in coqFileProgressParams
        ):
            return None
        textDocument = VersionedTextDocumentIdentifier(
            coqFileProgressParams["textDocument"]["uri"],
            coqFileProgressParams["textDocument"]["version"],
        )
        processing = []
        for progress in coqFileProgressParams["processing"]:
            processing.append(
                CoqFileProgressProcessingInfo(
                    Range(**progress["range"]),
                    (
                        None
                        if "kind" not in progress
                        else CoqFileProgressKind(progress["kind"])
                    ),
                )
            )
        return CoqFileProgressParams(textDocument, processing)
