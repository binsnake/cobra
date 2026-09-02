"""Shared fixtures and helpers."""

from __future__ import annotations

import os
import random
import shutil
import subprocess
from pathlib import Path

import pytest

from cobra_mba import Expr

REPO_ROOT = Path(__file__).resolve().parents[2]
DATASETS = REPO_ROOT / "datasets"


def cobra_cli() -> str | None:
    """Locate a built `cobra-cli`, if there is one to compare against."""
    override = os.environ.get("COBRA_CLI")
    if override:
        return override if Path(override).exists() else None
    for profile in ("release", "debug"):
        for name in ("cobra-cli.exe", "cobra-cli"):
            candidate = REPO_ROOT / "target" / profile / name
            if candidate.exists():
                return str(candidate)
    return shutil.which("cobra-cli")


@pytest.fixture(scope="session")
def cli() -> str:
    """Path to `cobra-cli`, skipping the test when it has not been built."""
    path = cobra_cli()
    if path is None:
        pytest.skip("cobra-cli is not built; run cargo build --bin cobra-cli --features cli")
    return path


def run_cli(cli_path: str, expression: str, bitwidth: int = 64) -> str:
    """Simplify one expression with the command-line program."""
    proc = subprocess.run(
        [cli_path, "--mba", expression, "--bitwidth", str(bitwidth)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"cobra-cli failed on {expression!r}: {proc.stderr.strip()}")
    return proc.stdout.strip()


def probe_equal(left: Expr, right: Expr, samples: int = 64, seed: int = 0x5EED) -> bool:
    """Compare two expressions over sampled full-width points.

    The same idea as the Rust test kit's full-width probe: exhaustive checking
    is impossible, so agreement is sampled. Both expressions must share a
    variable table, which is what the simplifier's remapping guarantees.
    """
    if left.variables != right.variables:
        return False
    rng = random.Random(seed)
    widths = left.variable_widths
    edges = [0, 1, 2, 3]
    for _ in range(samples):
        point = []
        for width in widths:
            top = (1 << width) - 1
            choice = rng.randrange(4)
            if choice == 0:
                point.append(rng.choice(edges) & top)
            elif choice == 1:
                point.append(top)
            elif choice == 2:
                point.append((top - rng.choice(edges)) & top)
            else:
                point.append(rng.randrange(top + 1))
        if left.evaluate(point) != right.evaluate(point):
            return False
    return True


def parse_dataset(body: str) -> list[tuple[int, str, str]]:
    """Read a dataset file the way the Rust test kit reads it.

    Lines starting with `#` and blank lines are skipped. A top-level tab
    separates input from expected; otherwise the line is a comma-separated
    list of equivalent forms whose first entry is the obfuscated input and
    whose last is the canonical form.
    """
    cases: list[tuple[int, str, str]] = []
    for number, raw in enumerate(body.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        tab = top_level_split(line, "\t")
        if len(tab) == 2:
            cases.append((number, tab[0].strip(), tab[1].strip()))
            continue
        parts = top_level_split(line, ",")
        if len(parts) >= 2:
            cases.append((number, parts[0].strip(), parts[-1].strip()))
    return cases


def top_level_split(line: str, separator: str) -> list[str]:
    """Split on `separator`, ignoring occurrences inside parentheses."""
    parts: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(line):
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char == separator and depth == 0:
            parts.append(line[start:index])
            start = index + 1
    parts.append(line[start:])
    return parts
