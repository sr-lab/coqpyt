from coqlspclient.coq_lsp_structs import ProofStep
from coqlspclient.coq_lsp_structs import CoqError, CoqErrorCodes
from coqlspclient.coq_file import CoqFile
from coqlspclient.aux_file import AuxFile
from typing import List


class ProofState(object):
    """Abstraction to interact with the proofs of a Coq file

    Attributes:
        coq_file (CoqFile): Coq file to interact with
    """

    def __init__(self, coq_file: CoqFile):
        """Creates a ProofState

        Args:
            coq_file (CoqFile): Coq file to interact with

        Raises:
            CoqError: If the provided file is not valid.
        """
        self.coq_file = coq_file
        if not self.coq_file.is_valid:
            self.coq_file.close()
            raise CoqError(
                CoqErrorCodes.InvalidFile,
                f"At least one error found in file {coq_file.path}",
            )
        self.coq_file.context = AuxFile.get_context(coq_file.path, coq_file.timeout)
        self.__aux_file = AuxFile(timeout=coq_file.timeout)
        self.__current_step = None

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __get_term(self, name):
        for i in range(len(self.coq_file.curr_module), -1, -1):
            curr_name = ".".join(self.coq_file.curr_module[:i] + [name])
            if curr_name in self.coq_file.context.terms:
                return self.coq_file.context.terms[curr_name]
            elif curr_name in self.coq_file.context.aliases:
                return self.coq_file.context.terms[
                    self.coq_file.context.aliases[curr_name]
                ]
        return None

    def __locate(self, search, line):
        nots = self.__aux_file.get_diagnostics("Locate", f'"{search}"', line).split("\n")
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
                term = self.__get_term(id)
                return [] if term is None else [(lambda x: x, term)]
            elif isinstance(el, list) and len(el) == 4 and el[0] == "CNotation":
                line = len(self.__aux_file.read().split("\n"))
                self.__aux_file.append(f'\nLocate "{el[2][1]}".')
                return [(self.__locate, el[2][1], line)] + traverse_ast(el[1:])
            elif isinstance(el, list):
                return [x for v in el for x in traverse_ast(v)]

            return []

        return traverse_ast(self.__current_step.ast.span)

    def __step(self):
        self.__current_step = self.coq_file.exec()[0]
        self.__aux_file.append(self.__current_step.text)

    def __get_steps(self):
        def trim_step_text():
            range = self.__current_step.ast.range
            nlines = range.end.line - range.start.line
            text = self.__current_step.text.split("\n")[-nlines:]
            text[0] = text[0][range.start.character :]
            return "\n".join(text)

        steps = []
        while self.coq_file.in_proof():
            try:
                goals = self.coq_file.current_goals()
            except Exception as e:
                self.__aux_file.close()
                raise e

            self.__step()
            text = trim_step_text()
            context_calls = self.__step_context()
            steps.append((text, goals, context_calls))
        return steps

    def get_proofs(self) -> List[List[ProofStep]]:
        """Gets all the proofs in the file and their corresponding steps.

        Returns:
            List[ProofStep]: Each element has the list of steps for a single 
                proof of the Coq file. The proofs are ordered by the order 
                they are written on the file.
        """
        def get_proof_step(step):
            context, calls = [], [call[0](*call[1:]) for call in step[2]]
            [context.append(call) for call in calls if call not in context]
            return ProofStep(step[0], step[1], context)

        proofs = []
        while not self.coq_file.checked():
            self.__step()
            if self.coq_file.in_proof():
                proofs.append(self.__get_steps())

        try:
            self.__aux_file.didOpen()
        except Exception as e:
            self.coq_file.close()
            raise e

        return [list(map(get_proof_step, steps)) for steps in proofs]

    def close(self):
        """Closes all resources used by this object. 
        """
        self.coq_file.close()
        self.__aux_file.close()
