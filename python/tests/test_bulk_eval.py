"""Bulk numeric evaluation."""

from __future__ import annotations

import random
import struct

import pytest

import cobra_mba
from cobra_mba import Expr

def pack(values: list[int]) -> bytes:
    """The raw column form: one little-endian 64-bit value per point."""
    return struct.pack(f"<{len(values)}Q", *values)


def test_matches_one_point_at_a_time() -> None:
    expr = Expr.parse("(x ^ y) + 2 * (x & y)")
    rng = random.Random(11)
    xs = [rng.getrandbits(64) for _ in range(500)]
    ys = [rng.getrandbits(64) for _ in range(500)]

    bulk = expr.evaluate_many({"x": xs, "y": ys})
    one_at_a_time = [expr.evaluate(x=a, y=b) for a, b in zip(xs, ys)]

    assert bulk == one_at_a_time


def test_accepts_columns_by_position() -> None:
    expr = Expr.parse("x + y")

    assert expr.evaluate_many([[1, 2, 3], [10, 20, 30]]) == [11, 22, 33]


def test_accepts_raw_byte_columns() -> None:
    expr = Expr.parse("x + y")
    xs, ys = [1, 2, 3], [10, 20, 30]

    assert expr.evaluate_many({"x": pack(xs), "y": pack(ys)}) == [11, 22, 33]
    assert expr.evaluate_many({"x": bytearray(pack(xs)), "y": pack(ys)}) == [11, 22, 33]


def test_raw_results_round_trip() -> None:
    expr = Expr.parse("x + y")
    raw = expr.evaluate_many({"x": [1, 2, 3], "y": [10, 20, 30]}, raw=True)

    assert isinstance(raw, bytes)
    assert list(struct.unpack("<3Q", raw)) == [11, 22, 33]


def test_values_are_reduced_to_their_width() -> None:
    expr = Expr.parse("x + 1", 8)

    assert expr.evaluate_many({"x": [255, 254, -1]}) == [0, 255, 0]


def test_mixed_width_variables_use_their_own_widths() -> None:
    narrow = Expr.var("a", width=8)
    expr = narrow.zext(32) + Expr.var("b", width=8).zext(32)

    assert expr.evaluate_many({"a": [200, 1], "b": [100, 1]}) == [300, 2]


def test_every_column_needs_the_same_length() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="same number of points"):
        expr.evaluate_many({"x": [1, 2, 3], "y": [1, 2]})


def test_a_missing_column_is_reported() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="no values given"):
        expr.evaluate_many({"x": [1, 2, 3]})


def test_an_unknown_column_is_reported() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="not a variable"):
        expr.evaluate_many({"x": [1], "y": [2], "z": [3]})


def test_wrong_column_count_by_position() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="expected 2 value columns"):
        expr.evaluate_many([[1, 2, 3]])


def test_a_string_is_not_a_set_of_columns() -> None:
    with pytest.raises(TypeError, match="not a string"):
        Expr.parse("x + y").evaluate_many("ab")  # type: ignore[arg-type]


def test_a_ragged_raw_column_is_rejected() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="8-byte values"):
        expr.evaluate_many({"x": b"12345", "y": pack([1])})


def test_a_constant_expression_has_nothing_to_vary() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError, match="no variables"):
        Expr.const(7).evaluate_many({})


def test_empty_columns_give_empty_results() -> None:
    expr = Expr.parse("x + y")

    assert expr.evaluate_many({"x": [], "y": []}) == []


def test_deep_expressions_stay_within_the_worker_stack() -> None:
    x = Expr.var("x")
    deep = x
    for _ in range(400):
        deep = deep + x

    assert deep.evaluate_many({"x": [1, 2]}) == [401, 802]


class TestNumpy:
    """The recipe the README and examples give for NumPy."""

    def setup_method(self) -> None:
        self.np = pytest.importorskip("numpy")

    def test_arrays_round_trip_through_bytes(self) -> None:
        np = self.np
        expr = Expr.parse("(x ^ y) + 2 * (x & y)")
        xs = np.arange(1000, dtype=np.uint64)
        ys = np.arange(1000, dtype=np.uint64) * 3

        raw = expr.evaluate_many({"x": xs.tobytes(), "y": ys.tobytes()}, raw=True)
        got = np.frombuffer(raw, dtype="<u8")

        assert got.shape == (1000,)
        assert np.array_equal(got, xs + ys)

    def test_a_plain_array_works_through_the_sequence_path(self) -> None:
        np = self.np
        expr = Expr.parse("x + y")
        xs = np.array([1, 2, 3], dtype=np.int64)

        assert expr.evaluate_many({"x": xs.tolist(), "y": [10, 20, 30]}) == [11, 22, 33]
