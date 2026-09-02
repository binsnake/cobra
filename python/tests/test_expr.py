"""The expression type: building, inspecting, evaluating, and serialising."""

from __future__ import annotations

import pickle

import pytest

import cobra_mba
from cobra_mba import Expr, Kind

BUILDER_CASES = [
    "x + y",
    "x * y",
    "x & y",
    "x | y",
    "x ^ y",
    "~x",
    "-x",
    "x - y",
    "(x ^ y) + 2 * (x & y)",
    "(x | y) - (x & y)",
    "x >> 3",
    "x << 2",
    "x ** 3",
    "a + b + c",
    "(a & b) | (a & c)",
]


def build(text: str) -> Expr:
    """Build the same expression with operators instead of the parser."""
    x, y = Expr.var("x"), Expr.var("y")
    a, b, c = Expr.var("a"), Expr.var("b"), Expr.var("c")
    built: dict[str, Expr] = {
        "x + y": x + y,
        "x * y": x * y,
        "x & y": x & y,
        "x | y": x | y,
        "x ^ y": x ^ y,
        "~x": ~x,
        "-x": -x,
        "x - y": x - y,
        "(x ^ y) + 2 * (x & y)": (x ^ y) + 2 * (x & y),
        "(x | y) - (x & y)": (x | y) - (x & y),
        "x >> 3": x >> 3,
        "x << 2": x << 2,
        "x ** 3": x**3,
        "a + b + c": a + b + c,
        "(a & b) | (a & c)": (a & b) | (a & c),
    }
    return built[text]


@pytest.mark.parametrize("text", BUILDER_CASES)
def test_builder_matches_the_parser(text: str) -> None:
    parsed = Expr.parse(text)
    built = build(text)

    assert built == parsed, f"{text}: built {built!s} but parsed {parsed!s}"
    assert hash(built) == hash(parsed)
    assert str(built) == str(parsed)


def test_variables_are_sorted_lexicographically() -> None:
    # The parser sorts, so the builder must sort the same way for the two to
    # produce equal trees.
    assert (Expr.var("b") + Expr.var("a")).variables == ["a", "b"]
    assert Expr.parse("b + a").variables == ["a", "b"]
    assert Expr.var("b") + Expr.var("a") == Expr.parse("b + a")


def test_variable_tables_merge_across_independently_built_trees() -> None:
    left = Expr.var("x") + Expr.var("z")
    right = Expr.var("y") * Expr.var("x")
    combined = left + right

    assert combined.variables == ["x", "y", "z"]
    assert combined == Expr.parse("(x + z) + (y * x)")


def test_merging_rejects_one_name_at_two_widths() -> None:
    # Reached through casts, since two bare variables of different widths are
    # caught by the bitwidth check first.
    def widened(name: str, width: int, other: str) -> Expr:
        state = {
            "bitwidth": 32,
            "variables": sorted([name, other]),
            "variable_widths": [
                width if n == name else 32 for n in sorted([name, other])
            ],
            "expr": {
                "kind": "add",
                "children": [
                    {
                        "kind": "zext",
                        "width": 32,
                        "children": [
                            {"kind": "variable", "index": sorted([name, other]).index(name)}
                        ],
                    },
                    {"kind": "variable", "index": sorted([name, other]).index(other)},
                ],
            },
        }
        return Expr.from_dict(state)

    left = widened("x", 8, "y")
    right = widened("x", 16, "z")

    assert left.variable_widths[left.variables.index("x")] == 8
    assert right.variable_widths[right.variables.index("x")] == 16
    with pytest.raises(cobra_mba.InvalidArgumentError, match="bits wide"):
        left + right


def test_mismatched_bitwidths_are_rejected() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError, match="different bitwidths"):
        Expr.var("x", width=8) + Expr.var("y", width=16)


def test_a_constant_adopts_its_partners_width() -> None:
    narrow = Expr.var("x", width=8)
    combined = narrow + Expr.const(511)

    assert combined.bitwidth == 8
    # 511 does not fit in 8 bits, so it is reduced the way the parser reduces
    # an out-of-range literal.
    assert combined.children[1].value == 511 & 0xFF


def test_too_many_variables_is_rejected() -> None:
    names = [f"v{i:02d}" for i in range(21)]
    total = Expr.var(names[0])
    with pytest.raises(cobra_mba.TooManyVariablesError):
        for name in names[1:]:
            total = total + Expr.var(name)


def test_node_inspection() -> None:
    expr = Expr.parse("(x ^ y) + 2 * (x & y)")

    assert expr.kind == Kind.ADD
    assert len(expr.children) == 2
    assert expr.children[0].kind == Kind.XOR
    assert expr.children[1].kind == Kind.MUL

    constant = expr.children[1].children[0]
    assert constant.kind == Kind.CONSTANT
    assert constant.value == 2
    assert constant.variable_index is None

    variable = expr.children[0].children[0]
    assert variable.kind == Kind.VARIABLE
    assert variable.variable_index == 0
    assert variable.variable_name == "x"


def test_shift_and_cast_payloads() -> None:
    assert Expr.parse("x >> 3").shift_amount == 3
    assert Expr.var("x", width=8).zext(32).target_width == 32
    assert Expr.var("x", width=8).zext(32).kind == Kind.ZEXT
    assert Expr.parse("x").shift_amount is None
    assert Expr.parse("x").target_width is None


def test_evaluate_accepts_three_shapes() -> None:
    expr = Expr.parse("(x ^ y) + 2 * (x & y)")

    assert expr.evaluate(x=3, y=5) == 8
    assert expr.evaluate({"x": 3, "y": 5}) == 8
    assert expr.evaluate([3, 5]) == 8


def test_evaluate_reduces_modulo_the_width() -> None:
    expr = Expr.parse("x + 1", 8)

    assert expr.evaluate(x=255) == 0
    assert expr.evaluate(x=-1) == 0


def test_evaluate_rejects_missing_and_unknown_variables() -> None:
    expr = Expr.parse("x + y")

    with pytest.raises(cobra_mba.InvalidArgumentError, match="no value given"):
        expr.evaluate(x=1)
    with pytest.raises(cobra_mba.InvalidArgumentError, match="not a variable"):
        expr.evaluate(x=1, y=2, z=3)
    with pytest.raises(cobra_mba.InvalidArgumentError, match="expected 2 values"):
        expr.evaluate([1])


def test_signature_length_follows_the_variable_count() -> None:
    assert len(Expr.parse("x").signature()) == 2
    assert len(Expr.parse("x + y").signature()) == 4
    assert len(Expr.parse("x + y + z").signature()) == 8


def test_render_round_trips_through_the_parser() -> None:
    for text in BUILDER_CASES:
        expr = Expr.parse(text)
        assert Expr.parse(expr.render()) == expr


def test_to_dict_round_trip() -> None:
    expr = Expr.parse("(x ^ y) + 2 * (x & y)")
    state = expr.to_dict()

    assert state["bitwidth"] == 64
    assert state["variables"] == ["x", "y"]
    assert state["expr"]["kind"] == "add"
    assert Expr.from_dict(state) == expr


def test_to_dict_is_plain_data() -> None:
    import json

    expr = Expr.parse("x + 1")
    assert Expr.from_dict(json.loads(json.dumps(expr.to_dict()))) == expr


def test_pickling() -> None:
    expr = Expr.parse("(x ^ y) + 2 * (x & y)", 32)
    revived = pickle.loads(pickle.dumps(expr))

    assert revived == expr
    assert revived.bitwidth == 32
    assert revived.variables == expr.variables


def test_equality_and_hashing_account_for_names_and_width() -> None:
    assert Expr.parse("x + y") == Expr.parse("x + y")
    assert Expr.parse("x + y") != Expr.parse("a + b")
    assert Expr.parse("x + y", 32) != Expr.parse("x + y", 64)
    assert Expr.parse("x + y") != "x + y"
    assert len({Expr.parse("x + y"), Expr.parse("x + y")}) == 1


def test_variable_names_must_be_identifiers() -> None:
    for bad in ["", "1x", "a-b", "a b", "x!"]:
        with pytest.raises(cobra_mba.InvalidArgumentError, match="usable variable name"):
            Expr.var(bad)


def test_mixed_width_trees_build_and_evaluate() -> None:
    narrow = Expr.var("a", width=8)
    widened = narrow.zext(32)

    assert widened.width == 32
    assert widened.bitwidth == 8
    assert widened.evaluate(a=200) == 200

    signed = narrow.sext(32)
    assert signed.evaluate(a=200) == 0xFFFFFFC8

    truncated = Expr.var("b", width=32).trunc(8)
    assert truncated.width == 8
    assert truncated.evaluate(b=0x1234) == 0x34


def test_concat_sums_widths() -> None:
    high = Expr.var("h", width=8)
    low = Expr.var("l", width=8)
    joined = Expr.concat(high, low)

    assert joined.width == 16
    assert joined.evaluate(h=0x12, l=0x34) == 0x1234


def test_casts_reject_the_wrong_direction() -> None:
    wide = Expr.var("w", width=32)

    with pytest.raises(cobra_mba.InvalidArgumentError, match="narrowing extension"):
        wide.zext(8)
    with pytest.raises(cobra_mba.InvalidArgumentError, match="widening truncation"):
        Expr.var("n", width=8).trunc(32)
    with pytest.raises(cobra_mba.InvalidArgumentError, match="more than 64 bits"):
        Expr.concat(Expr.var("p", width=64), Expr.var("q", width=64))


def test_shifts_stay_inside_the_bitwidth() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError, match="out of range"):
        Expr.parse("x", 8) >> 8
    with pytest.raises(cobra_mba.InvalidArgumentError, match="out of range"):
        Expr.parse("x", 8) << 8


def test_exponent_limit_matches_the_parser() -> None:
    # The parser caps `**` at 4096; the builder has to accept exactly as much.
    assert Expr.var("x") ** 100 == Expr.parse("x ** 100")
    with pytest.raises(cobra_mba.InvalidArgumentError, match="exceeds limit"):
        Expr.var("x") ** 4097
    with pytest.raises(cobra_mba.ParseError, match="exceeds limit"):
        Expr.parse("x ** 4097")


def test_evaluate_rejects_a_string_of_values() -> None:
    with pytest.raises(TypeError, match="not a string"):
        Expr.parse("x + y").evaluate("ab")  # type: ignore[arg-type]


def test_integer_operands_work_on_both_sides() -> None:
    x = Expr.var("x")

    assert 2 * x == Expr.parse("2 * x")
    assert x * 2 == Expr.parse("x * 2")
    assert 1 + x == Expr.parse("1 + x")
    assert (5 - x) == Expr.parse("5 - x")
    assert (x - 5) == Expr.parse("x - 5")


def test_unsupported_operands_defer_to_python() -> None:
    with pytest.raises(TypeError):
        Expr.var("x") + "y"  # type: ignore[operator]
    with pytest.raises(TypeError):
        Expr.var("x") & 1.5  # type: ignore[operator]


def test_deeply_nested_expressions_do_not_overflow_the_stack() -> None:
    # CPython gives its threads a 1 MiB stack on Windows; the binding runs the
    # pipeline on a 64 MiB worker so trees like this stay safe.
    x = Expr.var("x")
    deep = x
    for _ in range(500):
        deep = deep + x

    assert deep.evaluate(x=1) == 501
    assert deep.render().count("+") == 500
    assert deep.simplify().original is not None
