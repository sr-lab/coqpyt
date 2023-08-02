#!/usr/bin/env python
import sys

from setuptools import setup, find_packages
from setuptools.command.test import test as TestCommand

with open("README.md", "r") as fh:
    long_description = fh.read()


class PyTest(TestCommand):
    user_options = [("pytest-args=", "a", "Arguments to pass to pytest")]

    def initialize_options(self):
        TestCommand.initialize_options(self)
        self.pytest_args = []

    def run_tests(self):
        # import here, cause outside the eggs aren't loaded
        import pytest

        errno = pytest.main(self.pytest_args)
        sys.exit(errno)


setup(
    name="coq-lsp-pyclient",
    version="0.0.1",
    author="Pedro Carrott, Nuno Saavedra, Avi Yeger",
    author_email="pedro.carrott@tecnico.ulisboa.pt",
    description="Python client for coq-lsp",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/sr-lab/coq-lsp-pyclient",
    packages=find_packages(),
    tests_require=["pytest", "pytest_mock"],
    cmdclass={"test": PyTest},
)
