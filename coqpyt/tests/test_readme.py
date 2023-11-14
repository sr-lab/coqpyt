import os
import uuid
import pytest
import tempfile
import subprocess

temp_path = os.path.join(tempfile.gettempdir(), str(uuid.uuid4()))


@pytest.fixture
def teardown_aux():
    yield
    if os.path.exists(temp_path):
        os.remove(temp_path)


def test_readme_example(teardown_aux):
    readme_path = "../examples/readme"
    with open(f"{readme_path}.py", "r") as f:
        script, vfile = f.read(), f"{readme_path}.v"
        script = vfile.join(script.split(vfile[3:]))
        with open(temp_path, "w") as f2:
            f2.write(script)
        run = subprocess.run(f"python3 {temp_path}", shell=True, capture_output=True)
        assert run.returncode == 0
