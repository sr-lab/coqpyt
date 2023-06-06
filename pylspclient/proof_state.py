import os
from pylspclient.lsp_structs import TextDocumentItem, TextDocumentIdentifier

class ProofState(object):
    def __init__(self, coq_lsp_client, file_path, ast):
        self.path = file_path
        with open(file_path, "r") as f:
            self.lines = f.read().split('\n')
        self.ast = ast['spans']
        self.coq_lsp_client = coq_lsp_client
        self.current_step = None
        self.in_proof = False
    
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
            self.current_step = self.ast.pop(0)

            if self.__get_expr(self.current_step)[0] == 'VernacProof':
                self.in_proof = True
            elif self.__get_expr(self.current_step)[0] == 'VernacEndProof':
                self.in_proof = False

    def next_steps(self):
        if not self.in_proof:
            return None

        start_line = self.current_step['range']['end']['line']
        start_character = self.current_step['range']['end']['character']

        for step in self.ast:
            if self.__get_expr(step)[0] == 'VernacEndProof':
                break

        end_line = step['range']['end']['line']
        end_character = step['range']['end']['character']

        curr_text = self.lines[start_line:end_line + 1]
        curr_text[0] = curr_text[0][start_character:]
        curr_text[-1] = curr_text[-1][:end_character + 1]

        return '\n'.join(curr_text)
    
    def get_current_theorem(self):
        expr = self.__get_expr(self.current_step)
        if expr[0] != 'VernacStartTheoremProof':
            return None
        name = self.__get_theorem_name(expr)
        return self.__check(name)
    
    def jump_to_theorem(self):
        while self.__get_expr(self.current_step)[0] != 'VernacStartTheoremProof': 
            self.exec()
        return self.get_current_theorem()

    def jump_to_proof(self):
        while not self.in_proof: self.exec()