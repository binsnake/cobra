"""The runnable examples have to keep working.

An example that has drifted out of date is worse than no example, so the two
that do not need a reverse-engineering tool installed are run here.
"""

from __future__ import annotations

import ast
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import DATASETS, REPO_ROOT

EXAMPLES = REPO_ROOT / "python" / "examples"
TOOL_SCRIPTS = ["idapython_simplify.py", "binaryninja_simplify.py"]


def run_example(name: str, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(EXAMPLES / name), *args],
        capture_output=True,
        text=True,
        check=False,
        cwd=EXAMPLES,
    )


def test_bulk_evaluate_runs() -> None:
    done = run_example("bulk_evaluate.py", "--points", "2000")

    assert done.returncode == 0, done.stderr
    assert "evaluate_many, lists" in done.stdout
    assert "agree on all 2,000 points: True" in done.stdout


def test_simplify_corpus_runs() -> None:
    corpus = DATASETS / "univariate64.txt"
    if not corpus.exists():
        pytest.skip("bundled datasets are not present")

    done = run_example("simplify_corpus.py", str(corpus), "--limit", "40")

    assert done.returncode == 0, done.stderr
    assert "disagreed    0" in done.stdout
    assert "cases        40" in done.stdout


def test_simplify_corpus_reports_the_gate() -> None:
    corpus = DATASETS / "univariate64.txt"
    if not corpus.exists():
        pytest.skip("bundled datasets are not present")

    relaxed = run_example("simplify_corpus.py", str(corpus), "--limit", "40")
    strict = run_example(
        "simplify_corpus.py", str(corpus), "--limit", "40", "--certified-only"
    )

    assert relaxed.returncode == 0 and strict.returncode == 0
    assert "simplified   40" in relaxed.stdout
    assert "simplified   0" in strict.stdout


def test_simplify_corpus_rejects_a_missing_file() -> None:
    done = run_example("simplify_corpus.py", "no-such-corpus.txt")

    assert done.returncode == 1
    assert "no such file" in done.stderr


@pytest.mark.parametrize("name", TOOL_SCRIPTS)
def test_tool_scripts_are_valid_python(name: str) -> None:
    # These import a reverse-engineering tool's own modules, so they cannot be
    # executed here. Parsing them at least catches syntax rot.
    source = (EXAMPLES / name).read_text(encoding="utf-8")
    ast.parse(source, filename=name)


@pytest.mark.parametrize("name", TOOL_SCRIPTS)
def test_tool_scripts_say_they_are_untested(name: str) -> None:
    # The README makes this claim; the scripts have to carry it too, because a
    # reader may open one without the README.
    source = (EXAMPLES / name).read_text(encoding="utf-8").lower()

    assert "has not been run against a live" in source


def test_every_example_is_listed_in_the_readme() -> None:
    readme = (EXAMPLES / "README.md").read_text(encoding="utf-8")
    scripts = sorted(p.name for p in EXAMPLES.glob("*.py"))

    assert scripts, "no examples found"
    for name in scripts:
        assert name in readme, f"{name} is not mentioned in examples/README.md"


def test_binaryninja_example_imports_without_the_tool() -> None:
    # The import guard has to hold, or the script cannot even be inspected on a
    # machine without Binary Ninja.
    done = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys; sys.path.insert(0, r'%s'); import binaryninja_simplify as m;"
            " print(m.binaryninja)" % EXAMPLES,
        ],
        capture_output=True,
        text=True,
        check=False,
    )

    assert done.returncode == 0, done.stderr
    assert "None" in done.stdout
