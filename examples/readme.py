import os

from coqpyt.coq.structs import TermType
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile

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
