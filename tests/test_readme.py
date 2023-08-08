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

def test_if_readme_runs(teardown_aux):
    with open("README.md", "r") as f:
        text = f.read()
        script = text.split("```python")[1].split("```")[0]
        with open(temp_path, "w") as f2:
            f2.write(script)
        run = subprocess.run(f"python3 {temp_path}", shell=True, capture_output=True)
        assert run.returncode == 0