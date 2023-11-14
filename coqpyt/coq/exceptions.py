class InvalidChangeException(Exception):
    pass


class InvalidStepException(InvalidChangeException):
    def __init__(self, step: str):
        self.step: str = step

    def __str__(self):
        return "The step {} is not valid.".format(self.step)


class InvalidDeleteException(InvalidChangeException):
    def __init__(self, step_to_delete: str):
        self.step_to_delete: str = step_to_delete

    def __str__(self):
        return "Deleting the step {} is not valid.".format(self.delete)


class InvalidFileException(Exception):
    def __init__(self, file: str):
        self.file: str = file

    def __str__(self):
        return "The file {} is not valid.".format(self.file)


class NotationNotFoundException(Exception):
    def __init__(self, notation: str):
        self.notation: str = notation

    def __str__(self):
        return 'Notation "{}" not found in context.'.format(self.notation)
