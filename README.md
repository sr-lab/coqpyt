![Logo](https://github.com/sr-lab/coqpyt/blob/main/images/logo.png?raw=true)

Interact with Coq files and navigate through your proofs using our Python client for [coq-lsp](https://github.com/ejgallego/coq-lsp).

Execute Coq files, retrieve the generated context and edit proofs through insertion and removal of steps.

## Installation

[coq-lsp](https://github.com/ejgallego/coq-lsp) must be installed on version >= 0.1.7. Follow the installation instructions provided [here](https://github.com/ejgallego/coq-lsp#%EF%B8%8F-installation).

```bash
pip install -r requirements.txt
```

```bash
python -m pip install -e .
```

## Usage

![UML](https://github.com/sr-lab/coqpyt/blob/main/images/uml.png?raw=true)

Import classes from the ``coqpyt`` package.

<!-- embedme examples/readme.py#L3-L7 -->
```py
```

### Interaction with Coq

Create a CoqFile object, execute the file and extract the generated context.

<!-- embedme examples/readme.py#L9-L36 -->
```py
```

Create a ProofFile object (a CoqFile instance) and interact with the proofs.

<!-- embedme examples/readme.py#L38-L75 -->
```py
```

### Proof Modification

Given an admitted proof:

<!-- embedme examples/readme.v#L13-L19 -->
```coq
```

Perform step-wise changes to the proof.

<!-- embedme examples/readme.py#L87-L110 -->
```py
```

Perform changes to the proof transactionally.

<!-- embedme examples/readme.py#L113-L137 -->
```py
```

## Tests

To run the tests for CoqPyt go to the folder ``coqpyt`` and run:
```bash
pytest tests -s
```

## Contributing

Pull requests are welcome. 

For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.

## Credits

Special thanks to the developers of the [pylspclient](https://github.com/yeger00/pylspclient) project, which served as the initial template for CoqPyt. Additionally, we express our gratitude to [Kyle Thompson](https://github.com/rkthomps/) for his precious feedback, which has greatly contributed to the refinement of CoqPyt.

## License

[MIT](https://choosealicense.com/licenses/mit/)