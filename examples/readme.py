import os

from coqpyt.coq.structs import TermType
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import ProofAppend, ProofPop
from coqpyt.coq.exceptions import InvalidChangeException

# Open Coq file
with CoqFile(os.path.join(os.getcwd(), "examples/readme.v")) as coq_file:
    coq_file.exec(nsteps=2)
    # Get all terms defined until now
    print("Number of terms:", len(coq_file.context.terms))
    # Filter by Tactics
    print(
        "Number of tactics:",
        len(
            list(
                filter(
                    lambda term: term.type == TermType.TACTIC,
                    coq_file.context.terms.values(),
                )
            )
        ),
    )

    # Save compiled file
    coq_file.save_vo()
    print("Compiled file exists:", os.path.exists("examples/readme.vo"))
    os.remove("examples/readme.vo")

    # Run remaining file
    coq_file.run()
    print("Checked:", coq_file.checked)
    # Get all terms defined until now
    print("Number of terms:", len(coq_file.context.terms))

# Open Proof file
with ProofFile(os.path.join(os.getcwd(), "examples/readme.v")) as proof_file:
    # Enter proof
    proof_file.exec(nsteps=4)
    print("In proof:", proof_file.in_proof)
    # Get current goals
    print(proof_file.current_goals)

    # Run remaining file
    proof_file.run()
    # Number of proofs in the file
    print("Number of proofs:", len(proof_file.proofs))
    print("Proof:", proof_file.proofs[0].text)

    # Print steps of proof
    for step in proof_file.proofs[0].steps:
        print(step.text, end="")
    print()

    # Get the context used in the third step
    print(proof_file.proofs[0].steps[2].context)
    # Print the goals in the third step
    print(proof_file.proofs[0].steps[2].goals)

    # Print number of terms in context
    print("Number of terms:", len(proof_file.context.terms))
    # Filter for Notations only
    print(
        "Number of notations:",
        len(
            list(
                filter(
                    lambda term: term.type == TermType.NOTATION,
                    proof_file.context.terms.values(),
                )
            )
        ),
    )


def reset_proof(file: ProofFile):
    file.run()
    proven = file.proofs[1]
    file.pop_step(proven)
    file.pop_step(proven)
    file.pop_step(proven)
    file.append_step(proven, "\nAdmitted.")


with ProofFile(os.path.join(os.getcwd(), "examples/readme.v")) as proof_file:
    proof_file.run()
    # Get the first admitted proof
    unproven = proof_file.unproven_proofs[0]
    # Steps for an incorrect proof
    incorrect = [" reflexivity.", "\nQed."]
    # Steps for a correct proof
    correct = [" rewrite app_assoc."] + incorrect

    # Loop through both attempts
    for attempt in [incorrect, correct]:
        # Remove the "\nAdmitted." step
        proof_file.pop_step(unproven)
        try:
            # Append all steps in the attempt
            for i, s in enumerate(attempt):
                proof_file.append_step(unproven, s)
            print("Proof succeeded!")
            break
        except InvalidChangeException:
            # Some step was invalid, so we rollback the previous changes
            [proof_file.pop_step(unproven) for _ in range(i)]
            proof_file.append_step(unproven, "\nAdmitted.")
            print("Proof attempt not valid.")
    reset_proof(proof_file)

with ProofFile(os.path.join(os.getcwd(), "examples/readme.v")) as proof_file:
    proof_file.run()
    # Get the first admitted proof
    unproven = proof_file.unproven_proofs[0]
    # Steps for an incorrect proof
    incorrect = [" reflexivity.", "\nQed."]
    # Steps for a correct proof
    correct = [" rewrite app_assoc."] + incorrect

    # Loop through both attempts
    for attempt in [incorrect, correct]:
        # Schedule the removal of the "\nAdmitted." step
        changes = [ProofPop()]
        # Schedule the addition of each step in the attempt
        for s in attempt:
            changes.append(ProofAppend(s))
        try:
            # Apply all changes in one batch
            proof_file.change_proof(unproven, changes)
            print("Proof succeeded!")
            break
        except InvalidChangeException:
            # Some batch of changes was invalid
            # Rollback is automatic, so no rollback needed
            print("Proof attempt not valid.")
    reset_proof(proof_file)
