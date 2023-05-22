from pylspclient.lsp_structs import Position

class ProofState(object):
    def __init__(self, text):
        self.lines = text.split('\n')
        self.pos = Position(0, 0)
    
    def exec(self, steps=1):
        for _ in range(steps):
            found_dot = False
            for line in self.lines[self.pos.line:]:
                for char in line[self.pos.character:]:
                    if found_dot:
                        if char.isspace(): break
                        else: found_dot = False

                    if char == '.': found_dot = True
                    self.pos.character += 1

                if found_dot: break
                self.pos.line += 1
                self.pos.character = 0


    def is_in_proof(self):
        prev_text = '\n'.join(self.lines[:self.pos.line])
        prev_text += '\n' + self.lines[self.pos.line][:self.pos.character]

        if 'Proof.' not in prev_text:
            return False
        proofs = prev_text.split('Proof.')

        last_proof = proofs[-1]
        words = last_proof.split('.')

        for word in words:
            if 'Qed' in word:
                return False
            
        return True

    def next_steps(self):
        if not self.is_in_proof():
            return None

        curr_text = '\n'.join(self.lines[self.pos.line:])
        curr_text = curr_text[self.pos.character:]
        words = curr_text.split('.')
        next_steps = []

        for word in words:
            if not word[0].isspace():
                next_steps[-1] += word + '.'
            else:
                next_steps.append(word + '.')
                if "Qed" in word:
                    break

        return next_steps