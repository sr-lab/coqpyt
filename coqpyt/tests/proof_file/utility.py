import os
import re
import shutil
import subprocess
import tempfile
import uuid
import yaml

from abc import ABC, abstractmethod
from typing import Tuple, List, Dict, Union, Any

from coqpyt.coq.proof_file import ProofFile, ProofStep, ProofTerm
from coqpyt.coq.structs import TermType, Term
from coqpyt.coq.lsp.structs import *


class SetupProofFile(ABC):
    def setup(self, file_path, workspace=None):
        if workspace is not None:
            self.workspace = os.path.join(
                tempfile.gettempdir(), "test" + str(uuid.uuid4()).replace("-", "")
            )
            shutil.copytree(os.path.join("tests/resources", workspace), self.workspace)
            run = subprocess.run(
                f"cd {self.workspace} && make", shell=True, capture_output=True
            )
            assert run.returncode == 0
            self.file_path = os.path.join(self.workspace, os.path.basename(file_path))
        else:
            self.workspace = None
            new_path = os.path.join(
                tempfile.gettempdir(),
                "test" + str(uuid.uuid4()).replace("-", "") + ".v",
            )
            shutil.copyfile(os.path.join("tests/resources", file_path), new_path)
            self.file_path = new_path

        uri = "file://" + self.file_path
        self.proof_file = ProofFile(
            self.file_path, timeout=60, workspace=self.workspace
        )
        self.proof_file.run()
        self.versionId = VersionedTextDocumentIdentifier(uri, 1)

        output = subprocess.check_output(f"coqtop -v", shell=True)
        self.coq_version = output.decode("utf-8").split("\n")[0].split()[-1]

    @abstractmethod
    def setup_method(self, method):
        pass

    def teardown_method(self, method):
        if self.workspace is not None:
            subprocess.run(
                f"cd {self.workspace} && make clean", shell=True, capture_output=True
            )
        self.proof_file.close()
        os.remove(self.file_path)


def compare_context(
    test_context: List[Tuple[str, TermType, List[str]]], context: List[Term]
):
    assert len(test_context) == len(context)
    for i in range(len(context)):
        assert test_context[i][0] == context[i].text
        assert test_context[i][1] == context[i].type
        assert test_context[i][2] == context[i].module


def check_context(test_context: List[Dict[str, Union[str, List]]], context: List[Term]):
    assert len(test_context) == len(context)
    for i in range(len(context)):
        assert test_context[i]["text"] == context[i].text
        assert TermType[test_context[i]["type"]] == context[i].type
        if "module" not in test_context[i]:
            test_context[i]["module"] = []
        assert test_context[i]["module"] == context[i].module


def check_goal(test_goal: Dict, goal: Goal):
    assert test_goal["ty"] == goal.ty
    assert len(test_goal["hyps"]) == len(goal.hyps)
    for j in range(len(goal.hyps)):
        assert test_goal["hyps"][j]["ty"] == goal.hyps[j].ty
        assert len(test_goal["hyps"][j]["names"]) == len(goal.hyps[j].names)
        for k in range(len(goal.hyps[j].names)):
            assert test_goal["hyps"][j]["names"][k] == goal.hyps[j].names[k]


def check_step(test_step: Dict[str, Any], step: ProofStep):
    assert test_step["text"] == step.text
    goals = test_step["goals"]

    assert goals["position"]["line"] == step.goals.position.line
    assert goals["position"]["character"] == step.goals.position.character
    assert len(goals["messages"]) == len(step.goals.messages)
    for i in range(len(step.goals.messages)):
        assert goals["messages"][i] == step.goals.messages[i].text

    assert len(goals["goals"]["goals"]) == len(step.goals.goals.goals)
    for i in range(len(step.goals.goals.goals)):
        check_goal(goals["goals"]["goals"][i], step.goals.goals.goals[i])

    # Check stack
    assert len(goals["goals"]["stack"]) == len(step.goals.goals.stack)
    for i in range(len(step.goals.goals.stack)):
        assert len(goals["goals"]["stack"][i][0]) == len(step.goals.goals.stack[i][0])
        for j in range(len(step.goals.goals.stack[i][0])):
            check_goal(
                goals["goals"]["stack"][i][0][j], step.goals.goals.stack[i][0][j]
            )

        assert len(goals["goals"]["stack"][i][1]) == len(step.goals.goals.stack[i][1])
        for j in range(len(step.goals.goals.stack[i][1])):
            check_goal(
                goals["goals"]["stack"][i][1][j], step.goals.goals.stack[i][1][j]
            )

    # Check shelf
    assert len(goals["goals"]["shelf"]) == len(step.goals.goals.shelf)
    for i in range(len(step.goals.goals.shelf)):
        check_goal(goals["goals"]["shelf"][i], step.goals.goals.shelf[i])

    # Check given_up
    assert len(goals["goals"]["given_up"]) == len(step.goals.goals.given_up)
    for i in range(len(step.goals.goals.given_up)):
        check_goal(goals["goals"]["given_up"][i], step.goals.goals.given_up[i])

    check_context(test_step["context"], step.context)

    if "range" in test_step:
        test_range = test_step["range"]
        step_range = step.ast.range
        assert test_range["start"]["line"] == step_range.start.line
        assert test_range["start"]["character"] == step_range.start.character
        assert test_range["end"]["line"] == step_range.end.line
        assert test_range["end"]["character"] == step_range.end.character


def check_proof(test_proof: Dict, proof: ProofTerm):
    check_context(test_proof["context"], proof.context)
    assert len(test_proof["steps"]) == len(proof.steps)
    if "program" in test_proof:
        assert proof.program is not None
        assert test_proof["program"] == proof.program.text
    for j, step in enumerate(test_proof["steps"]):
        check_step(step, proof.steps[j])


def check_proofs(
    yaml_file: str, proofs: List[ProofTerm], coq_version: Optional[str] = None
):
    test_proofs = get_test_proofs(yaml_file, coq_version)
    assert len(proofs) == len(test_proofs["proofs"])
    for i, test_proof in enumerate(test_proofs["proofs"]):
        check_proof(test_proof, proofs[i])


def add_step_defaults(step):
    if "goals" not in step:
        step["goals"] = {}
    if "messages" not in step["goals"]:
        step["goals"]["messages"] = []
    if "goals" not in step["goals"]:
        step["goals"]["goals"] = {}
    if "goals" not in step["goals"]["goals"]:
        step["goals"]["goals"]["goals"] = []
    if "stack" not in step["goals"]["goals"]:
        step["goals"]["goals"]["stack"] = []
    if "shelf" not in step["goals"]["goals"]:
        step["goals"]["goals"]["shelf"] = []
    if "given_up" not in step["goals"]["goals"]:
        step["goals"]["goals"]["given_up"] = []
    if "context" not in step:
        step["context"] = []


def get_context_by_version(context: List[Dict[str, Any]], coq_version: str):
    res = []

    for term in context:
        for key in term:
            if re.match(key.replace("x", "[0-9]+"), coq_version):
                res.append(term[key])
                break
        else:
            res.append(term["default"] if "default" in term else term)

    return res


def get_test_proofs(yaml_file: str, coq_version: Optional[str] = None):
    with open(yaml_file, "r") as f:
        test_proofs = yaml.safe_load(f)
    for test_proof in test_proofs["proofs"]:
        if "context" not in test_proof:
            test_proof["context"] = []
        if coq_version is not None:
            test_proof["context"] = get_context_by_version(
                test_proof["context"], coq_version
            )
        for step in test_proof["steps"]:
            add_step_defaults(step)
    return test_proofs
