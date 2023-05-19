from pylspclient.lsp_structs import Position

class ProofState(object):
    def __init__(self, text):
        self.text = text
        self.i = 0
        self.pos = Position(0, 0)
    
    def exec(self, steps=1):
        for _ in range(steps):
            while True:
                if self.text[self.i] == '\n':
                    self.pos.line += 1
                    self.pos.character = 0
                    self.i += 1
                else:
                    self.pos.character += 1
                    self.i += 1
                    if self.text[self.i-1] == '.' and self.text[self.i].isspace():
                        break