# CoqPyt

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

Import classes from the ``coqpyt`` package.

<!-- embedme examples/readme.py#L2-L4 -->
```py
```

Create a CoqFile object, execute the file and extract the generated context.

<!-- embedme examples/readme.py#L7-L39 -->
```py
```

Create a ProofFile object (a CoqFile instance) and interact with the proofs.

<!-- embedme examples/readme.py#L42-L70 -->
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

## License

[MIT](https://choosealicense.com/licenses/mit/)