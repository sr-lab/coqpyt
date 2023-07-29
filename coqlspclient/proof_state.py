from coqlspclient.coq_lsp_structs import ProofStep
from coqlspclient.coq_lsp_structs import CoqError, CoqErrorCodes
from coqlspclient.coq_file import CoqFile
from coqlspclient.aux_file import AuxFile


class ProofState(object):
    def __init__(self, file_path, timeout=2):
        self.coq_file = CoqFile(file_path, timeout=timeout)
        if not self.coq_file.is_valid:
            self.coq_file.close()
            raise CoqError(CoqErrorCodes.InvalidFile, f"At least one error found in file {file_path}")
        self.coq_file.context = AuxFile.get_context(file_path, timeout)
        self.aux_file = AuxFile(timeout=timeout)
        self.current_step = None

    def __get_term(self, name):
        for i in range(len(self.coq_file.curr_module), -1, -1):
            curr_name = ".".join(self.coq_file.curr_module[:i] + [name])
            if curr_name in self.coq_file.context.terms:
                return self.coq_file.context.terms[curr_name]
            elif curr_name in self.coq_file.context.aliases:
                return self.coq_file.context.terms[self.coq_file.context.aliases[curr_name]]
        return None

    def __locate(self, search, line):
        nots = self.aux_file.get_diagnostics("Locate", f'"{search}"', line).split("\n")
        fun = lambda x: x.endswith("(default interpretation)")
        if len(nots) > 1:
            return list(filter(fun, nots))[0][:-25]
        else:
            return nots[0][:-25] if fun(nots[0]) else nots[0]

    def __step_context(self):
        def traverse_ast(el):
            if isinstance(el, dict):
                return [x for v in el.values() for x in traverse_ast(v)]
            elif isinstance(el, list) and len(el) == 3 and el[0] == "Ser_Qualid":
                id = ".".join([l[1] for l in el[1][1][::-1]] + [el[2][1]])
                return [(lambda x: x, self.__get_term(id))]
            elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                line = len(self.aux_file.read().split("\n"))
                self.aux_file.append(f"\nLocate \"{el[2][1]}\".")
                return [(self.__locate, el[2][1], line)] + traverse_ast(el[1:])
            elif isinstance(el, list):
                return [x for v in el for x in traverse_ast(v)]

            return []

        res, traversed = [], traverse_ast(self.current_step.ast.span)
        [res.append(x) for x in traversed if x not in res]
        return res

    def __step(self):
        self.current_step = self.coq_file.exec()[0]
        self.aux_file.append(self.current_step.text)

    def __pre_proof_steps(self):
        def trim_step_text():
            range = self.current_step.ast.range
            nlines = range.end.line - range.start.line
            text = self.current_step.text.split("\n")[-nlines:]
            text[0] = text[0][range.start.character:]
            return "\n".join(text)

        pre_proof_steps = []
        while self.coq_file.in_proof():
            goals = self.coq_file.current_goals()
            self.__step()
            text = trim_step_text()
            context_calls = self.__step_context()
            pre_proof_steps.append((text, goals, context_calls))
        return pre_proof_steps

    def get_proofs(self):
        pre_proofs = []
        while not self.coq_file.checked():
            self.__step()
            if self.coq_file.in_proof():
                pre_proofs.append(self.__pre_proof_steps())
        self.aux_file.didOpen()

        proofs = []
        for pre_proof_steps in pre_proofs:
            proof_steps = []
            for step in pre_proof_steps:
                context = [call[0](*call[1:]) for call in step[2]]
                filtered, context = filter(lambda x: x is not None, context), []
                [context.append(x) for x in filtered if x not in context]
                proof_steps.append(ProofStep(step[0], step[1], context))
            proofs.append(proof_steps)

        return proofs

    def close(self):
        self.coq_file.close()
        self.aux_file.close()
