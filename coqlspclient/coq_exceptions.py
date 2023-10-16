class InvalidStepException(Exception):
    def __init__(self, step: str):
        self.step: str = step

    def __str__(self):
        return "The step {} is not valid.".format(self.step)


class InvalidFileException(Exception):
    def __init__(self, file: str):
        self.file: str = file

    def __str__(self):
        return "The file {} is not valid.".format(self.file)
