import pytest


def pytest_addoption(parser):
    parser.addoption(
        "--runextra", action="store_true", default=False, help="run extra tests from external libraries"
    )


def pytest_configure(config):
    config.addinivalue_line("markers", "extra: mark test as from external library")


def pytest_collection_modifyitems(config, items):
    if config.getoption("--runextra"):
        return
    skip_extra = pytest.mark.skip(reason="need --runextra option to run")
    for item in items:
        if "extra" in item.keywords:
            item.add_marker(skip_extra)

