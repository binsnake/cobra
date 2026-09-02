"""Batch simplification across the worker pool."""

from __future__ import annotations

import pytest

import cobra_mba
from cobra_mba import Expr, Options, OutcomeKind, simplify_many

CORPUS = [
    "(x ^ y) + 2 * (x & y)",
    "(x | y) - (x & y)",
    "x + y",
    "(a & b) + (a | b)",
    "(x ^ y) ^ y",
    "a + b + c",
    "x * y + x",
    "~(~x)",
]


def test_batch_matches_one_at_a_time() -> None:
    batched = [str(result) for result in simplify_many(CORPUS)]
    serial = [str(cobra_mba.simplify(case)) for case in CORPUS]

    assert batched == serial


def test_results_come_back_in_input_order() -> None:
    # Work is handed out to whichever thread is free, so ordering is a
    # property of the merge rather than of the scheduling.
    corpus = CORPUS * 12
    results = simplify_many(corpus, workers=8)

    assert len(results) == len(corpus)
    assert [str(r) for r in results] == [str(cobra_mba.simplify(c)) for c in corpus]


def test_accepts_expressions_and_a_mix() -> None:
    mixed: list[str | Expr] = ["(x ^ y) + 2 * (x & y)", Expr.parse("(x | y) - (x & y)")]
    results = simplify_many(mixed)

    assert [str(r) for r in results] == ["x + y", "x ^ y"]


def test_an_empty_batch_is_an_empty_list() -> None:
    assert simplify_many([]) == []


def test_accepts_any_iterable() -> None:
    results = simplify_many(case for case in CORPUS[:3])

    assert len(results) == 3


def test_worker_count_does_not_change_results() -> None:
    baseline = [str(r) for r in simplify_many(CORPUS, workers=1)]

    for workers in (2, 4, 16):
        assert [str(r) for r in simplify_many(CORPUS, workers=workers)] == baseline


def test_zero_workers_is_rejected() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError, match="at least 1"):
        simplify_many(CORPUS, workers=0)


def test_a_bad_item_raises_and_names_its_index() -> None:
    with pytest.raises(cobra_mba.ParseError, match="item 1"):
        simplify_many(["x + y", "bad +", "a + b"])


def test_the_earliest_failure_is_the_one_reported() -> None:
    # Threads finish out of order, so the reported failure has to be chosen by
    # index rather than by whichever landed first.
    corpus = ["x + y"] * 20 + ["bad +"] + ["also bad ++"] + ["x + y"] * 20

    for _ in range(5):
        with pytest.raises(cobra_mba.ParseError, match="item 20"):
            simplify_many(corpus, workers=8)


def test_errors_can_be_kept_in_place_instead() -> None:
    results = simplify_many(["x + y", "bad +", "a + b"], on_error="none")

    assert len(results) == 3
    assert results[1] is None
    assert results[0] is not None and str(results[0]) == "x + y"
    assert results[2] is not None and str(results[2]) == "a + b"


def test_on_error_rejects_anything_else() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError, match="on_error"):
        simplify_many(CORPUS, on_error="ignore")  # type: ignore[call-overload]


def test_non_expressions_are_a_type_error() -> None:
    with pytest.raises(TypeError, match="item 1"):
        simplify_many(["x + y", 42])  # type: ignore[list-item]


def test_the_batch_runs_at_one_width() -> None:
    narrow = Expr.parse("x + y", 8)

    with pytest.raises(cobra_mba.InvalidArgumentError, match="8-bit expression"):
        simplify_many([narrow])

    assert str(simplify_many([narrow], bitwidth=8)[0]) == "x + y"


def test_options_reach_the_batch() -> None:
    strict = simplify_many(["x * x * x"], bitwidth=32)
    relaxed = simplify_many(["x * x * x"], bitwidth=32, require_lean_certificate=False)

    assert relaxed[0].kind == OutcomeKind.SIMPLIFIED
    assert strict[0].original.bitwidth == 32


def test_results_carry_full_diagnostics() -> None:
    result = simplify_many(["(x ^ y) + 2 * (x & y)"])[0]

    assert result.telemetry.total_expansions > 0
    assert result.variables == ["x", "y"]
    assert result.expr is not None
    assert str(result.original) == "(x ^ y) + 2 * (x & y)"


def test_native_entry_point_takes_an_options_object() -> None:
    from cobra_mba._native import simplify_many as native

    results = native(["x + y"], Options(bitwidth=16), None, "raise")

    assert results[0].original.bitwidth == 16
