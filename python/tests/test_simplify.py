"""The one-shot entry point and the shape of what it returns."""

from __future__ import annotations

import pytest

import cobra_mba
from cobra_mba import Expr, Options, OutcomeKind, ProofLevel, SemanticClass


def test_readme_example_round_trip() -> None:
    result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")

    assert str(result) == "x + y"
    assert result.simplified is True
    assert result.kind == OutcomeKind.SIMPLIFIED
    assert result.proof_level == ProofLevel.LEAN_CERTIFIED
    assert result.verified is True
    assert result.variables == ["x", "y"]
    assert result.expr is not None
    assert str(result.expr) == "x + y"


def test_result_carries_the_original() -> None:
    result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")

    assert str(result.original) == "(x ^ y) + 2 * (x & y)"
    assert result.original.variables == ["x", "y"]


def test_signature_is_reported() -> None:
    result = cobra_mba.simplify("x + y")

    assert result.signature == Expr.parse("x + y").signature()


def test_diagnostic_is_populated() -> None:
    result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")
    diagnostic = result.diagnostic

    assert diagnostic.semantic_class == SemanticClass.LINEAR
    assert cobra_mba.StructuralFlags.HAS_ARITHMETIC in diagnostic.structural_flags
    assert isinstance(diagnostic.reason, str)
    assert isinstance(diagnostic.cause_chain, tuple)


def test_telemetry_shows_the_pipeline_ran() -> None:
    result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")

    assert result.telemetry.total_expansions > 0
    assert result.telemetry.candidates_verified > 0
    assert "total_expansions" in repr(result.telemetry)


@pytest.mark.parametrize("bitwidth", list(range(1, 65)))
def test_every_supported_bitwidth_accepts_a_variable(bitwidth: int) -> None:
    result = cobra_mba.simplify("x", bitwidth=bitwidth)

    assert str(result) == "x"
    assert result.original.bitwidth == bitwidth


@pytest.mark.parametrize("bitwidth", [0, 65, 128])
def test_bitwidths_outside_the_range_are_rejected(bitwidth: int) -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError):
        cobra_mba.simplify("x", bitwidth=bitwidth)


def test_simplify_accepts_an_expression() -> None:
    built = Expr.parse("(x ^ y) + 2 * (x & y)", 32)
    result = cobra_mba.simplify(built)

    assert str(result) == "x + y"
    # The expression's own width is used when none is given.
    assert result.original.bitwidth == 32


def test_relaxing_the_certificate_gate_widens_what_simplifies() -> None:
    # The gate is what stands between probe-only assurance and a replayable
    # proof, so at minimum turning it off must never lose a result.
    strict = cobra_mba.simplify("(x | y) - (x & y)")
    relaxed = cobra_mba.simplify("(x | y) - (x & y)", require_lean_certificate=False)

    assert relaxed.kind == OutcomeKind.SIMPLIFIED
    if strict.kind == OutcomeKind.SIMPLIFIED:
        assert strict.proof_level == ProofLevel.LEAN_CERTIFIED


def test_relaxed_gate_returns_results_below_lean_certified() -> None:
    # Turning the gate off is what admits results the certificate machinery
    # could not cover, so they arrive with weaker evidence attached.
    corpus = [
        "x * x * x",
        "(x ^ y) * (x | y)",
        "x * y + x * y",
        "(a & b) * (a | b)",
        "x + y * y * y",
        "(x ^ y) + 2 * (x & y) + z * z",
    ]
    levels = {
        cobra_mba.simplify(case, require_lean_certificate=False).proof_level
        for case in corpus
    }

    assert levels & {
        ProofLevel.UNVERIFIED,
        ProofLevel.SPOT_CHECKED,
    }, f"expected weaker evidence somewhere, got {levels}"


def test_options_round_trip() -> None:
    options = Options(bitwidth=32, max_vars=8, require_lean_certificate=False)

    assert options.bitwidth == 32
    assert options.max_vars == 8
    assert options.require_lean_certificate is False
    assert options.spot_check is True
    assert options == Options(bitwidth=32, max_vars=8, require_lean_certificate=False)
    assert options != Options()
    assert "bitwidth=32" in repr(options)


def test_options_reject_a_bad_bitwidth() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError):
        Options(bitwidth=0)


def test_expression_simplify_uses_its_own_width_by_default() -> None:
    expr = Expr.parse("x + y", 8)

    assert expr.simplify().original.bitwidth == 8


def test_signature_entry_point() -> None:
    signature = Expr.parse("x + y").signature()
    result = cobra_mba.simplify_signature(signature, ["x", "y"])

    assert result.kind == OutcomeKind.SIMPLIFIED
    assert str(result) == "x + y"


def test_build_info_reports_the_version_and_features() -> None:
    info = cobra_mba.build_info()

    assert info["version"] == cobra_mba.__version__
    assert isinstance(info["features"], list)


def test_module_constants() -> None:
    assert cobra_mba.MAX_BITWIDTH == 64
    assert cobra_mba.MAX_VARIABLES == 20
    assert cobra_mba.MAX_INPUT_VARS == 20
    assert cobra_mba.DEFAULT_MAX_VARS == 16
