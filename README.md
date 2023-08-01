# coq-lsp-pyclient

Python client for [coq-lsp](https://github.com/ejgallego/coq-lsp).

Abstraction to interact with Coq files, get their context, execute them, among other operations.

## Installation

[coq-lsp](https://github.com/ejgallego/coq-lsp) must be installed. Follow the installaton instructions provided [here](https://github.com/ejgallego/coq-lsp#%EF%B8%8F-installation).

```bash
pip install -r requirements.txt
```

## Usage

```python
import os
from coqlspclient.coq_file import CoqFile
from coqlspclient.proof_state import ProofState

# Open Coq file
with CoqFile(os.path.join(os.getcwd(), "examples/example.v")) as coq_file:
    # Print AST
    print(coq_file.ast)
    # Enter proof
    coq_file.exec(nsteps=4)
    print("In proof:", coq_file.in_proof)
    # Get current goals
    print(coq_file.current_goals())

    # Save compiled file
    coq_file.save_vo()
    print("Compiled file exists:", os.path.exists("examples/example.vo"))
    os.remove("examples/example.vo")

    # Run remaining file
    coq_file.run()
    print("Checked:", coq_file.checked)

with CoqFile(os.path.join(os.getcwd(), "examples/example.v")) as coq_file:
    with ProofState(coq_file) as proof_state:
        # Number of proofs in the file
        print(len(proof_state.proofs))

        # Print steps of proof
        for step in proof_state.proofs[0]:
            print(step.text, end="")
        print()

        # Get the context used in the third step
        print(proof_state.proofs[0][2].context)
        # Print the goals in the third step
        print(proof_state.proofs[0][2].goals)

        # Print number of terms in context
        print(len(proof_state.context.terms))
        # Print number of notations in context
        print(len(proof_state.context.notations))
```

### Run tests

```bash
pytest tests -s
```

## Contributing

Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.

## License

[MIT](https://choosealicense.com/licenses/mit/)