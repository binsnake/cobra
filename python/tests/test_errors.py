"""Error mapping: every library error code reaches Python as its own class."""

from __future__ import annotations

import pytest

import cobra_mba
from cobra_mba import ErrorCode, Expr, OutcomeKind


def test_parse_failure_raises_parse_error() -> None:
    with pytest.raises(cobra_mba.ParseError) as info:
        Expr.parse("x +")

    error = info.value
    assert error.code == ErrorCode.PARSE_ERROR
    assert error.message
    assert str(error) == error.message


def test_bad_bitwidth_raises_invalid_argument() -> None:
    with pytest.raises(cobra_mba.InvalidArgumentError) as info:
        Expr.parse("x", 65)

    assert info.value.code == ErrorCode.INVALID_ARGUMENT


def test_too_many_variables_raises_its_own_class() -> None:
    names = " + ".join(f"v{i:02d}" for i in range(21))

    with pytest.raises(cobra_mba.TooManyVariablesError) as info:
        Expr.parse(names)

    assert info.value.code == ErrorCode.TOO_MANY_VARIABLES


@pytest.mark.parametrize(
    "exception",
    [
        cobra_mba.InvalidArgumentError,
        cobra_mba.ParseError,
        cobra_mba.TooManyVariablesError,
    ],
)
def test_input_errors_are_also_value_errors(exception: type[Exception]) -> None:
    assert issubclass(exception, cobra_mba.CobraError)
    assert issubclass(exception, ValueError)


@pytest.mark.parametrize(
    "exception",
    [
        cobra_mba.NonLinearInputError,
        cobra_mba.NoReductionError,
        cobra_mba.VerificationFailedError,
        cobra_mba.SimplificationError,
    ],
)
def test_other_errors_share_the_base_class(exception: type[Exception]) -> None:
    assert issubclass(exception, cobra_mba.CobraError)
    assert not issubclass(exception, ValueError)


def test_every_error_code_has_a_name() -> None:
    codes = [
        ErrorCode.INVALID_ARGUMENT,
        ErrorCode.PARSE_ERROR,
        ErrorCode.NON_LINEAR_INPUT,
        ErrorCode.TOO_MANY_VARIABLES,
        ErrorCode.NO_REDUCTION,
        ErrorCode.VERIFICATION_FAILED,
    ]

    assert len(set(codes)) == 6


def test_errors_can_be_caught_as_the_base_class() -> None:
    with pytest.raises(cobra_mba.CobraError):
        Expr.parse("(((")


def test_errors_can_be_caught_as_value_error() -> None:
    with pytest.raises(ValueError):
        Expr.parse("&&&")


def test_raise_for_error_is_quiet_on_success() -> None:
    result = cobra_mba.simplify("(x ^ y) + 2 * (x & y)")

    assert result.kind != OutcomeKind.ERROR
    result.raise_for_error()


def test_pipeline_errors_are_data_not_exceptions() -> None:
    # Anything the pipeline itself rejects comes back as an outcome so the
    # diagnostic survives; only bad input raises.
    result = cobra_mba.simplify("x * x * x", bitwidth=32)

    assert result.kind in {
        OutcomeKind.SIMPLIFIED,
        OutcomeKind.UNCHANGED_UNSUPPORTED,
        OutcomeKind.ERROR,
    }
    assert isinstance(result.diagnostic.reason, str)


def test_error_message_survives_on_the_exception() -> None:
    with pytest.raises(cobra_mba.CobraError) as info:
        Expr.parse("x", 0)

    assert "1..=64" in info.value.message
