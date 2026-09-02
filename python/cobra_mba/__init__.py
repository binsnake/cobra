"""CoBRA: a simplifier for mixed Boolean-arithmetic (MBA) expressions.

The quickest thing you can do with it::

    >>> import cobra_mba
    >>> str(cobra_mba.simplify("(x ^ y) + 2 * (x & y)"))
    'x + y'

Everything else hangs off :class:`Expr`, which pairs an expression tree with
the variable names its indices refer to::

    >>> from cobra_mba import Expr
    >>> x, y = Expr.var("x"), Expr.var("y")
    >>> built = (x ^ y) + 2 * (x & y)
    >>> built == Expr.parse("(x ^ y) + 2 * (x & y)")
    True
    >>> built.evaluate(x=3, y=5)
    8
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any, Literal, Union, overload

from ._native import (
    DEFAULT_MAX_VARS,
    MAX_BITWIDTH,
    MAX_INPUT_VARS,
    MAX_VARIABLES,
    CobraError,
    Diagnostic,
    ErrorCode,
    Expr,
    InvalidArgumentError,
    Kind,
    NoReductionError,
    NonLinearInputError,
    Options,
    OutcomeKind,
    ParseError,
    ProofLevel,
    ReasonCategory,
    ReasonCode,
    ReasonDomain,
    ReasonFrame,
    SemanticClass,
    SimplificationError,
    SimplifyResult,
    StructuralFlags,
    Telemetry,
    TooManyVariablesError,
    VerificationFailedError,
    __version__,
    build_info,
    simplify_signature,
)
from ._native import simplify_many as _simplify_many

__all__ = [
    "DEFAULT_MAX_VARS",
    "MAX_BITWIDTH",
    "MAX_INPUT_VARS",
    "MAX_VARIABLES",
    "CobraError",
    "Diagnostic",
    "ErrorCode",
    "Expr",
    "InvalidArgumentError",
    "Kind",
    "NoReductionError",
    "NonLinearInputError",
    "Options",
    "OutcomeKind",
    "ParseError",
    "ProofLevel",
    "ReasonCategory",
    "ReasonCode",
    "ReasonDomain",
    "ReasonFrame",
    "SemanticClass",
    "SimplificationError",
    "SimplifyResult",
    "StructuralFlags",
    "Telemetry",
    "TooManyVariablesError",
    "VerificationFailedError",
    "__version__",
    "build_info",
    "simplify",
    "simplify_many",
    "simplify_signature",
]


def simplify(
    expression: Union[str, Expr],
    *,
    bitwidth: Union[int, None] = None,
    max_vars: int = DEFAULT_MAX_VARS,
    spot_check: bool = True,
    enable_bitwise_decomposition: bool = True,
    structural_flags: int = 0,
    require_lean_certificate: bool = True,
) -> SimplifyResult:
    """Parse and simplify one expression.

    This is the whole pipeline in one call, and its string form matches what
    ``cobra-cli`` prints for the same input::

        >>> str(simplify("(x ^ y) + 2 * (x & y)"))
        'x + y'

    Args:
        expression: Text in the simplifier's infix syntax, or an
            already-built :class:`Expr`.
        bitwidth: Width to work at, 1 through 64. Defaults to 64 for text,
            and to the expression's own width for an :class:`Expr`.
        max_vars: Largest variable count any subproblem may reach.
        spot_check: Check candidates against sampled full-width probes.
        enable_bitwise_decomposition: Let the bitwise decomposition passes run.
        structural_flags: Structural shapes to assume, on top of what the
            classifier finds.
        require_lean_certificate: Discard any simplification without a
            replayable Lean certificate. On by default, and it is the
            soundness gate. Turning it off accepts probe-only assurance,
            which raises the simplification rate a great deal but can return
            an expression that is wrong at a point no probe reached.

    Returns:
        The outcome, including the diagnostic explaining anything that did
        not fire. Pipeline errors come back as
        ``SimplifyResult.kind == OutcomeKind.ERROR`` rather than as an
        exception; call
        :meth:`SimplifyResult.raise_for_error` to turn one into an exception.

    Raises:
        ParseError: The text could not be parsed.
        InvalidArgumentError: An argument was out of range.
        TooManyVariablesError: The expression has too many variables.
    """
    if isinstance(expression, Expr):
        expr = expression
        width = expr.bitwidth if bitwidth is None else bitwidth
    else:
        width = MAX_BITWIDTH if bitwidth is None else bitwidth
        expr = Expr.parse(expression, width)

    options = Options(
        bitwidth=width,
        max_vars=max_vars,
        spot_check=spot_check,
        enable_bitwise_decomposition=enable_bitwise_decomposition,
        structural_flags=structural_flags,
        require_lean_certificate=require_lean_certificate,
    )
    return expr.simplify(options)


@overload
def simplify_many(
    expressions: Iterable[Union[str, Expr]],
    *,
    bitwidth: int = ...,
    max_vars: int = ...,
    spot_check: bool = ...,
    enable_bitwise_decomposition: bool = ...,
    structural_flags: int = ...,
    require_lean_certificate: bool = ...,
    workers: Union[int, None] = ...,
    on_error: Literal["raise"] = ...,
) -> list[SimplifyResult]: ...


@overload
def simplify_many(
    expressions: Iterable[Union[str, Expr]],
    *,
    bitwidth: int = ...,
    max_vars: int = ...,
    spot_check: bool = ...,
    enable_bitwise_decomposition: bool = ...,
    structural_flags: int = ...,
    require_lean_certificate: bool = ...,
    workers: Union[int, None] = ...,
    on_error: Literal["none"],
) -> list[Union[SimplifyResult, None]]: ...


def simplify_many(
    expressions: Iterable[Union[str, Expr]],
    *,
    bitwidth: int = MAX_BITWIDTH,
    max_vars: int = DEFAULT_MAX_VARS,
    spot_check: bool = True,
    enable_bitwise_decomposition: bool = True,
    structural_flags: int = 0,
    require_lean_certificate: bool = True,
    workers: Union[int, None] = None,
    on_error: Literal["raise", "none"] = "raise",
) -> list[Any]:
    """Simplify many expressions on a pool of worker threads.

    Faster than calling :func:`simplify` in a loop for two reasons: the whole
    batch crosses into the extension once, and the work is spread over every
    core with the interpreter lock released.

        >>> results = simplify_many(["(x ^ y) + 2 * (x & y)", "(x | y) - (x & y)"])
        >>> [str(r) for r in results]
        ['x + y', 'x ^ y']

    Args:
        expressions: Expression strings, :class:`Expr` objects, or a mix.
        bitwidth: Width the whole batch runs at. An :class:`Expr` built at a
            different width is rejected rather than silently reinterpreted.
        max_vars: Largest variable count any subproblem may reach.
        spot_check: Check candidates against sampled full-width probes.
        enable_bitwise_decomposition: Let the bitwise decomposition passes run.
        structural_flags: Structural shapes to assume.
        require_lean_certificate: Discard any simplification without a
            replayable Lean certificate. See :func:`simplify`.
        workers: Thread count. Defaults to the number of available cores,
            capped at the number of items.
        on_error: ``"raise"`` reports the earliest failing item and stops;
            ``"none"`` puts ``None`` in its place so one bad input does not
            cost the batch.

    Returns:
        One result per input, in input order. Entries are ``None`` only where
        an item failed and ``on_error`` was ``"none"``.
    """
    options = Options(
        bitwidth=bitwidth,
        max_vars=max_vars,
        spot_check=spot_check,
        enable_bitwise_decomposition=enable_bitwise_decomposition,
        structural_flags=structural_flags,
        require_lean_certificate=require_lean_certificate,
    )
    return _simplify_many(expressions, options, workers, on_error)
