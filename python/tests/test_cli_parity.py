"""The binding and `cobra-cli` must print the same thing for the same input.

Both go through the same remapping helper on the Rust side, so this test is
what keeps the two from drifting apart.
"""

from __future__ import annotations

import pytest

import cobra_mba
from conftest import run_cli

CASES = [
    "(x ^ y) + 2 * (x & y)",
    "(x | y) - (x & y)",
    "x + y",
    "x",
    "x ^ x",
    "x & x",
    "~(~x)",
    "x - x",
    "a + b + c",
    "(a & b) + (a | b)",
    "(x ^ y) ^ y",
    "2 * x + 3 * x",
    "x * y + x * y",
    "(x & y) | (x & ~y)",
    "x >> 3",
    "x << 2",
    "x ** 2",
    "-x + x",
    "(a | b) & a",
    "x & ~x",
]


@pytest.mark.parametrize("expression", CASES)
def test_output_matches_the_cli(cli: str, expression: str) -> None:
    assert str(cobra_mba.simplify(expression)) == run_cli(cli, expression)


@pytest.mark.parametrize("bitwidth", [8, 16, 32, 64])
def test_output_matches_the_cli_at_other_widths(cli: str, bitwidth: int) -> None:
    expression = "(x ^ y) + 2 * (x & y)"

    assert str(cobra_mba.simplify(expression, bitwidth=bitwidth)) == run_cli(
        cli, expression, bitwidth
    )


def test_a_dropped_variable_renders_the_same(cli: str) -> None:
    # The case the shared remapping helper exists for: the result depends on
    # fewer variables than the input, so its indices need renumbering before
    # the caller's names can be attached.
    expression = "(x ^ y) + 2 * (x & y) - y"

    assert str(cobra_mba.simplify(expression)) == run_cli(cli, expression)
