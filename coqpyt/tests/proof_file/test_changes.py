import pytest

from coqpyt.coq.lsp.structs import *
from coqpyt.coq.exceptions import *
from coqpyt.coq.changes import *

from utility import *


class TestProofValidFile(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_valid.v")

    def test_delete_and_add(self):
        proof_file = self.proof_file
        proof_file.delete_step(6)

        test_proofs = get_test_proofs("tests/proof_file/expected/valid_file.yml", 2)
        test_proofs["proofs"][0]["steps"].pop(1)
        test_proofs["proofs"][0]["steps"][0]["goals"]["version"] = 1
        for i, step in enumerate(test_proofs["proofs"][0]["steps"]):
            if i != 0:
                step["goals"]["position"]["line"] -= 1
            if i != len(test_proofs["proofs"][0]["steps"]) - 1:
                step["goals"]["goals"]["goals"][0]["hyps"] = []
                step["goals"]["goals"]["goals"][0]["ty"] = "∀ n : nat, 0 + n = n"
        check_proof(test_proofs["proofs"][0], proof_file.proofs[0])

        proof_file.add_step(5, "\n      intros n.")

        test_proofs = get_test_proofs("tests/proof_file/expected/valid_file.yml", 3)
        test_proofs["proofs"][0]["steps"][0]["goals"]["version"] = 1
        check_proof(test_proofs["proofs"][0], proof_file.proofs[0])

        # Check if context is changed correctly
        proof_file.add_step(7, "\n      Print minus.")
        step = {
            "text": "\n      Print minus.",
            "goals": {
                "goals": {
                    "goals": [
                        {"hyps": [{"names": ["n"], "ty": "nat"}], "ty": "0 + n = n"}
                    ]
                },
                "position": {"line": 12, "character": 6},
            },
            "context": [
                {
                    "text": "Notation minus := Nat.sub (only parsing).",
                    "type": "NOTATION",
                }
            ],
        }
        add_step_defaults(step, 4)
        test_proofs["proofs"][0]["steps"].insert(3, step)
        for i, step in enumerate(test_proofs["proofs"][0]["steps"][4:]):
            step["goals"]["version"] = 4
            step["goals"]["position"]["line"] += 1
        check_proof(test_proofs["proofs"][0], proof_file.proofs[0])

        # Add step in beginning of proof
        proof_file.add_step(26, "\n    Print plus.")
        assert proof_file.steps[27].text == "\n    Print plus."

        # Add step to end of proof
        proof_file.add_step(31, "\n    Print plus.")
        assert proof_file.steps[32].text == "\n    Print plus."

        # Delete step in beginning of proof
        proof_file.delete_step(27)
        assert proof_file.steps[27].text == "\n      intros n."

        # Delete step in end of proof
        proof_file.delete_step(41)
        assert proof_file.steps[41].text == "\n    Admitted."

        # FIXME
        # Delete outside of proof
        # proof_file.delete_step(33)

        # Add outside of proof
        # proof_file.add_step(25, "\n    Print plus.")

    def test_invalid_changes(self):
        proof_file = self.proof_file
        n_old_steps = len(proof_file.steps)
        old_diagnostics = proof_file.diagnostics
        old_goals = []
        for proof in proof_file.proofs:
            for step in proof.steps:
                old_goals.append(step.goals)

        def check_rollback():
            with open(proof_file.path, "r") as f:
                assert n_old_steps == len(proof_file.steps)
                assert old_diagnostics == proof_file.diagnostics
                assert proof_file.is_valid
                assert "invalid_tactic" not in f.read()
                i = 0
                for proof in proof_file.proofs:
                    for step in proof.steps:
                        assert step.goals == old_goals[i]
                        i += 1

        with pytest.raises(InvalidDeleteException):
            proof_file.delete_step(9)
            check_rollback()
        with pytest.raises(InvalidDeleteException):
            proof_file.delete_step(16)
            check_rollback()
        with pytest.raises(InvalidStepException):
            proof_file.add_step(7, "invalid_tactic")
            check_rollback()
        with pytest.raises(InvalidStepException):
            proof_file.add_step(7, "invalid_tactic.")
            check_rollback()
        with pytest.raises(InvalidStepException):
            proof_file.add_step(7, "\n    invalid_tactic.")
            check_rollback()
        with pytest.raises(InvalidStepException):
            proof_file.add_step(7, "\n    invalid_tactic x $$$ y.")
            check_rollback()

    def test_change_steps(self):
        proof_file = self.proof_file
        proof_file.change_steps(
            [
                CoqDeleteStep(6),
                CoqAddStep("\n      intros n.", 5),
                CoqAddStep("\n      Print minus.", 7),
            ]
        )

        test_proofs = get_test_proofs("tests/proof_file/expected/valid_file.yml", 4)
        test_proofs["proofs"][0]["steps"][0]["goals"]["version"] = 1
        step = {
            "text": "\n      Print minus.",
            "goals": {
                "goals": {
                    "goals": [
                        {"hyps": [{"names": ["n"], "ty": "nat"}], "ty": "0 + n = n"}
                    ]
                },
                "position": {"line": 12, "character": 6},
            },
            "context": [
                {
                    "text": "Notation minus := Nat.sub (only parsing).",
                    "type": "NOTATION",
                }
            ],
        }
        add_step_defaults(step, 4)
        test_proofs["proofs"][0]["steps"].insert(3, step)
        for step in test_proofs["proofs"][0]["steps"][4:]:
            step["goals"]["position"]["line"] += 1
        check_proof(test_proofs["proofs"][0], proof_file.proofs[0])

        # Add outside of proof
        with pytest.raises(NotImplementedError):
            proof_file.change_steps([CoqAddStep("\n    Print plus.", 25)])

        # Add step in beginning of proof
        proof_file.change_steps([CoqAddStep("\n    Print plus.", 26)])
        assert proof_file.steps[27].text == "\n    Print plus."

        # # Delete outside of proof
        with pytest.raises(NotImplementedError):
            proof_file.change_steps([CoqDeleteStep(33)])

        # # Add step to end of proof
        proof_file.change_steps([CoqAddStep("\n    Print plus.", 31)])
        assert proof_file.steps[32].text == "\n    Print plus."

        # # Delete step in beginning of proof
        proof_file.change_steps([CoqDeleteStep(27)])
        assert proof_file.steps[27].text == "\n      intros n."

        # # Delete step in end of proof
        proof_file.change_steps([CoqDeleteStep(41)])
        assert proof_file.steps[41].text == "\n    Admitted."


class TestProofSimpleFileChanges(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_simple_file.v")

    def test_simple_file_changes(self):
        proof_file = self.proof_file
        proof_file.change_steps(
            [
                CoqDeleteStep(1),
                CoqDeleteStep(1),
                CoqDeleteStep(2),
                CoqDeleteStep(2),
                CoqDeleteStep(2),
                CoqAddStep("\nAdmitted.", 0),
                CoqAddStep("\nAdmitted.", 2),
            ]
        )
        assert len(proof_file.steps) == 5
        assert len(proof_file.proofs) == 2

        steps = [
            "Example test1: 1 + 1 = 2.",
            "\nAdmitted.",
            "\n\nExample test2: 1 + 1 + 1= 3.",
            "\nAdmitted.",
        ]
        for i, step in enumerate(steps):
            assert step == proof_file.steps[i].text

        assert proof_file.proofs[0].text == steps[0]
        assert proof_file.proofs[0].steps[0].text == steps[1]
        assert proof_file.proofs[1].text == steps[2].strip()
        assert proof_file.proofs[1].steps[0].text == steps[3]


class TestProofChangeWithNotation(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_change_with_notation.v")

    def test_change_with_notation(self):
        # Just checking if the program does not crash
        self.proof_file.add_step(len(self.proof_file.steps) - 3, " destruct (a <? n).")


class TestProofChangeInvalidFile(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_invalid_1.v")

    def test_change_invalid_file(self):
        with pytest.raises(InvalidFileException):
            self.proof_file.add_step(7, "Print plus.")


class TestProofChangeEmptyProof(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_change_empty.v")

    def test_change_empty_proof(self):
        proof_file = self.proof_file
        assert len(proof_file.proofs) == 0
        assert len(proof_file.open_proofs) == 1

        proof_file.add_step(len(proof_file.steps) - 2, "\nAdmitted.")
        assert proof_file.steps[-2].text == "\nAdmitted."
        assert len(proof_file.open_proofs[0].steps) == 2
        assert proof_file.open_proofs[0].steps[-1].text == "\nAdmitted."

        proof_file.delete_step(len(proof_file.steps) - 2)
        assert len(proof_file.steps) == 3
        assert len(proof_file.open_proofs[0].steps) == 1
