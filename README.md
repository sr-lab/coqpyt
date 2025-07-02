![Logo](https://github.com/sr-lab/coqpyt/blob/master/images/logo.png?raw=true)

Interact with Coq files and navigate through your proofs using our Python client for [coq-lsp](https://github.com/ejgallego/coq-lsp).

Execute Coq files, retrieve the generated context and edit proofs through insertion and removal of steps.

If you use CoqPyt in an article, please cite:

[CoqPyt: Proof Navigation in Python in the Era of LLMs](https://doi.org/10.1145/3663529.3663814)

```
@inproceedings{carrott2024coqpyt,
  title={CoqPyt: Proof Navigation in Python in the Era of LLMs},
  author={Carrott, Pedro and Saavedra, Nuno and Thompson, Kyle and Lerner, Sorin and Ferreira, Jo{\~a}o F and First, Emily},
  booktitle={Companion Proceedings of the 32nd ACM International Conference on the Foundations of Software Engineering},
  pages={637--641},
  year={2024}
}
```

## Installation

[Python](https://www.python.org/) must be installed on version >= 3.11.

[coq-lsp](https://github.com/ejgallego/coq-lsp) must be installed on version >= 0.1.7. Follow the installation instructions provided [here](https://github.com/ejgallego/coq-lsp#%EF%B8%8F-installation).

```bash
pip install -r requirements.txt
python -m pip install -e .
```

### uv installation

In alternative, use [uv](https://github.com/astral-sh/uv) to setup the project and create a virtual environment.

```bash
uv sync --dev
uv pip install -e .
```

## Usage

![UML](https://github.com/sr-lab/coqpyt/blob/master/images/uml.png?raw=true)

Import classes from the ``coqpyt`` package.

<!-- embedme examples/readme.py#L3-L7 -->
```py
from coqpyt.coq.structs import TermType
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import ProofAppend, ProofPop
from coqpyt.coq.exceptions import InvalidChangeException
```

### Interaction with Coq

Create a CoqFile object, execute the file and extract the generated context.

<!-- embedme examples/readme.py#L9-L36 -->
```py
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
```

Create a ProofFile object (a CoqFile instance) and interact with the proofs.

<!-- embedme examples/readme.py#L38-L75 -->
```py
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
```

### Proof Modification

Given an admitted proof:

<!-- embedme examples/readme.v#L13-L19 -->
```coq
Lemma rev_append: forall {a} (l1 l2: list a),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros a l1 l2. induction l1; intros. 
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1.
Admitted.
```

Perform step-wise changes to the proof.

<!-- embedme examples/readme.py#L87-L110 -->
```py
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
```

Perform changes to the proof transactionally.

<!-- embedme examples/readme.py#L113-L137 -->
```py
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
```

## Tests

To run the core tests for CoqPyt go to the folder ``coqpyt`` and run:
```bash
pytest tests -rs
```

Skipped tests require the following external Coq libraries to run successfully:
- [Coq-Equations](https://github.com/mattam82/Coq-Equations)

To run all tests go to the folder ``coqpyt`` and run:
```bash
pytest tests -rs --runextra
```

## Contributing

Pull requests are welcome. 

For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.

## Credits

Special thanks to the developers of the [pylspclient](https://github.com/yeger00/pylspclient) project, which served as the initial template for CoqPyt. Additionally, we express our gratitude to [Kyle Thompson](https://github.com/rkthomps/) for his precious feedback, which has greatly contributed to the refinement of CoqPyt.

## License

[MIT](https://choosealicense.com/licenses/mit/)
