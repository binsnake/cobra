"""A sampled pass over the bundled corpora.

The exhaustive run lives in the Rust `datasets` test. This one checks that the
binding drives the same corpora correctly: whatever the pipeline returns must
agree with the input over a full-width probe.

Sampling runs with the Lean certificate gate relaxed. With the gate on, almost
nothing in these corpora simplifies, which is the documented trade-off and is
covered separately below; running relaxed is what puts real results through the
probe check.
"""

from __future__ import annotations

import pytest

import cobra_mba
from cobra_mba import Expr, OutcomeKind, ProofLevel
from conftest import DATASETS, parse_dataset, probe_equal

# One file per shape of input, sampled rather than exhausted.
DATASET_FILES = [
    "univariate64.txt",
    "multivariate64.txt",
    "msimba.txt",
]
SAMPLE_STRIDE = 17
MAX_PER_FILE = 15


def load(name: str) -> list[tuple[int, str, str]]:
    path = DATASETS / name
    if not path.exists():
        return []
    cases = parse_dataset(path.read_text(encoding="utf-8", errors="replace"))
    return cases[::SAMPLE_STRIDE][:MAX_PER_FILE]


def collect() -> list[tuple[str, int, str, str]]:
    collected: list[tuple[str, int, str, str]] = []
    for name in DATASET_FILES:
        for number, source, expected in load(name):
            collected.append((name, number, source, expected))
    return collected


CASES = collect()
needs_datasets = pytest.mark.skipif(not CASES, reason="no bundled datasets found")


@needs_datasets
@pytest.mark.parametrize(
    ("name", "number", "source", "expected"),
    CASES,
    ids=[f"{n}:{ln}" for n, ln, _, _ in CASES],
)
def test_simplification_agrees_with_the_input(
    name: str, number: int, source: str, expected: str
) -> None:
    try:
        original = Expr.parse(source)
    except cobra_mba.CobraError:
        pytest.skip(f"{name}:{number} does not parse")

    result = cobra_mba.simplify(source, require_lean_certificate=False)

    if result.kind != OutcomeKind.SIMPLIFIED or result.expr is None:
        # Leaving an input alone is a valid outcome; only a wrong answer fails.
        return

    assert probe_equal(result.expr, original), (
        f"{name}:{number}: {source!r} simplified to {result.expr!s}, "
        "which disagrees with the input"
    )


@needs_datasets
def test_the_relaxed_gate_simplifies_most_of_the_corpus() -> None:
    # Guards against the sampling above quietly selecting only inputs the
    # pipeline declines, which would make the test above vacuous.
    simplified = sum(
        1
        for _, _, source, _ in CASES
        if cobra_mba.simplify(source, require_lean_certificate=False).kind
        == OutcomeKind.SIMPLIFIED
    )

    assert simplified > len(CASES) // 2, (
        f"only {simplified} of {len(CASES)} sampled cases simplified with the "
        "certificate gate relaxed"
    )


@needs_datasets
def test_the_certificate_gate_is_the_conservative_setting() -> None:
    # The gate discards any simplification without a replayable certificate,
    # so it can only ever return fewer results than the relaxed setting.
    strict = sum(
        1 for _, _, source, _ in CASES if cobra_mba.simplify(source).kind == OutcomeKind.SIMPLIFIED
    )
    relaxed = sum(
        1
        for _, _, source, _ in CASES
        if cobra_mba.simplify(source, require_lean_certificate=False).kind
        == OutcomeKind.SIMPLIFIED
    )

    assert strict <= relaxed


@needs_datasets
def test_relaxed_results_carry_weaker_evidence() -> None:
    # Turning the gate off means accepting results the certificate machinery
    # could not cover; those come back below LEAN_CERTIFIED.
    levels = {
        cobra_mba.simplify(source, require_lean_certificate=False).proof_level
        for _, _, source, _ in CASES
    }

    assert levels & {ProofLevel.UNVERIFIED, ProofLevel.SPOT_CHECKED}


def test_dataset_reader_handles_both_layouts() -> None:
    body = "\n".join(
        [
            "# a comment",
            "",
            "x+y\tx + y",
            "(x^y)+2*(x&y), x + y",
            "a, b, c",
        ]
    )
    cases = parse_dataset(body)

    assert cases == [
        (3, "x+y", "x + y"),
        (4, "(x^y)+2*(x&y)", "x + y"),
        (5, "a", "c"),
    ]
