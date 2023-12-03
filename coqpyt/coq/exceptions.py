class InvalidChangeException(Exception):
    pass


class InvalidAddException(InvalidChangeException):
    def __init__(self, step: str):
        self.step: str = step

    def __str__(self):
        return "Adding the step {} is not valid.".format(self.step)


class InvalidDeleteException(InvalidChangeException):
    def __init__(self, step: str):
        self.step: str = step

    def __str__(self):
        return "Deleting the step {} is not valid.".format(self.step)


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
