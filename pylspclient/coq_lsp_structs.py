class Hyp(object):
    def __init__(self, names, ty, definition=None):
        self.names = names
        self.ty = ty
        self.definition = definition


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
    def __init__(
        self, textDocument, position, messages, goals=None, error=None, program=[]
    ):
        self.textDocument = textDocument
        self.position = position
        self.messages = messages
        self.goals = goals
        self.error = error
        self.program = program

    def __repr__(self):
        def recursive_vars(obj):
            if obj is None or isinstance(obj, int) or isinstance(obj, str):
                return obj
            elif isinstance(obj, list):
                res = []
                for v in obj:
                    res.append(recursive_vars(v))
                return res
            else:
                res = dict(vars(obj))
                for key, v in res.items():
                    res[key] = recursive_vars(v)
                return res

        return str(recursive_vars(self))


class Result(object):
    def __init__(self, range, message):
        self.range = range
        self.message = message


class Query(object):
    def __init__(self, query, results):
        self.query = query
        self.results = results


class Step(object):
    def __init__(self, text, goals, context):
        self.text = text
        self.goals = goals
        self.context = context
