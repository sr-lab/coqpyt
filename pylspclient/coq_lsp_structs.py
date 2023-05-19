class Hyp(object):
    def __init__(self, names, ty, definition=None):
        self.names = names
        self.definition = definition
        self.ty = ty


class Goal(object):
    def __init__(self, hyps, ty):
        self.hyps = hyps
        self.ty = ty


class GoalConfig(object):
    def __init__(self, goals, stack, shelf, given_up, bullet=None):
        self.goals = goals
        self.stack = stack
        self.shelf = shelf
        self.given_up = given_up
        self.bullet = bullet


class Message(object):
    def __init__(self, level, text, range=None):
        self.level = level
        self.text = text
        self.range = range


class GoalAnswer(object):
    def __init__(self, textDocument, position, messages, goals=None, error=None, program=None):
        self.textDocument = textDocument
        self.position = position
        self.messages = messages
        self.goals = goals
        self.error = error
        self.program = program
