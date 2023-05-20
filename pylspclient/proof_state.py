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


    def is_in_proof(self):
        lines = self.text.split('\n')
        previous_text = '\n'.join(lines[:self.pos.line])
        previous_text += '\n' + lines[self.pos.line][:self.pos.character]

        if 'Proof.' not in previous_text:
            return False
        proofs = previous_text.split('Proof.')

        last_proof = proofs[-1]
        words = last_proof.split('.')

        for word in words:
            if 'Qed' in word:
                return False
            
        return True

    def next_steps(self):
        if not self.is_in_proof():
            return []

        curr_text = '\n'.join(self.text.split('\n')[self.pos.line:])
        curr_text = curr_text[self.pos.character:]
        words = curr_text.split('.')
        next_steps = []

        for word in words:
            next_steps.append(word)
            if "Qed" in word:
                break

        return '.'.join(next_steps) + '.'