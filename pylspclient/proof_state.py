import os
import shutil
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier
from pylspclient.lsp_structs import Position

class ProofState(object):
    def __init__(self, coq_lsp_client, file_path, ast):
        self.path = file_path
        with open(file_path, "r") as f:
            self.lines = f.read().split('\n')
        self.ast = ast['spans']
        self.coq_lsp_client = coq_lsp_client
        self.current_step = None
        self.in_proof = False
        self.pos = Position(0, 0)
    
    def __get_expr(self, ast_step):
        return ast_step['span']['v']['expr']
    
    def __get_theorem_name(self, expr):
        return expr[2][0][0][0]['v'][1]
    
    def __check(self, search):
        dir = os.path.dirname(self.path)
        new_base_name = os.path.basename(self.path).split('.')
        new_base_name = new_base_name[0] + "new." + new_base_name[1]
        new_path = os.path.join(dir, new_base_name)
        with open(new_path, 'w') as f:
            with open(self.path, 'r') as original:
                f.write(original.read() + f"\nCheck ({search}).")

        check = None
        with open(new_path, 'r') as f:
            uri = "file://" + new_path
            self.coq_lsp_client.didOpen(TextDocumentItem(uri, 'coq', 1, f.read()))

            for query in self.coq_lsp_client.get_queries(TextDocumentIdentifier(uri), "Check"):
                if query.query == '(' + search + ')':
                    check = query.results[0]
            self.coq_lsp_client.didClose(TextDocumentIdentifier(uri))
        
        os.remove(new_path)
        return check

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
            self.current_step = self.ast.pop(0)

            if self.__get_expr(self.current_step)[0] == 'VernacProof':
                self.in_proof = True
            elif self.__get_expr(self.current_step)[0] == 'VernacEndProof':
                self.in_proof = False

    def next_steps(self):
        if not self.in_proof:
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
    
    def get_new_theorem_or_lemma(self):
        expr = self.__get_expr(self.current_step)
        if expr[0] != 'VernacStartTheoremProof':
            return None
        name = self.__get_theorem_name(expr)
        return self.__check(name)
    
    def proof_steps(self, symbol):
        if symbol.detail not in ['Theorem', 'Lemma']:
            return None
        
        line = symbol.range['start']['line']
        self.pos = Position(line, 0)
        self.exec(2) # Theorem. and Proof.

        return self.next_steps()