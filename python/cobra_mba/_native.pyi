"""Type stubs for the native extension.

Checked against the compiled module by ``mypy.stubtest`` in CI, so the two
cannot drift apart.
"""

import enum
from collections.abc import Iterable, Mapping, Sequence
from typing import Any, Literal, Union, final, overload

__all__ = [
    "CobraError",
    "DEFAULT_MAX_VARS",
    "Diagnostic",
    "ErrorCode",
    "Expr",
    "InvalidArgumentError",
    "Kind",
    "MAX_BITWIDTH",
    "MAX_INPUT_VARS",
    "MAX_VARIABLES",
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
    "simplify_many",
    "simplify_signature",
]

__version__: str

# One column of values: a sequence of integers, or bytes holding
# little-endian 64-bit values.
_Column = Union[Sequence[int], bytes, bytearray]

MAX_BITWIDTH: int
MAX_VARIABLES: int
MAX_INPUT_VARS: int
DEFAULT_MAX_VARS: int

@final
class ErrorCode:
    INVALID_ARGUMENT: ErrorCode
    PARSE_ERROR: ErrorCode
    NON_LINEAR_INPUT: ErrorCode
    TOO_MANY_VARIABLES: ErrorCode
    NO_REDUCTION: ErrorCode
    VERIFICATION_FAILED: ErrorCode

@final
class Kind:
    CONSTANT: Kind
    VARIABLE: Kind
    ADD: Kind
    MUL: Kind
    AND: Kind
    OR: Kind
    XOR: Kind
    NOT: Kind
    NEG: Kind
    SHR: Kind
    ZEXT: Kind
    SEXT: Kind
    TRUNC: Kind
    CONCAT: Kind

@final
class OutcomeKind:
    SIMPLIFIED: OutcomeKind
    UNCHANGED_UNSUPPORTED: OutcomeKind
    ERROR: OutcomeKind

@final
class ProofLevel:
    UNVERIFIED: ProofLevel
    SPOT_CHECKED: ProofLevel
    SMT_PROVED: ProofLevel
    LEAN_CERTIFIED: ProofLevel

@final
class SemanticClass:
    LINEAR: SemanticClass
    SEMILINEAR: SemanticClass
    POLYNOMIAL: SemanticClass
    NON_POLYNOMIAL: SemanticClass

@final
class ReasonCategory:
    NONE: ReasonCategory
    GUARD_FAILED: ReasonCategory
    INAPPLICABLE: ReasonCategory
    REPRESENTATION_GAP: ReasonCategory
    NO_SOLUTION: ReasonCategory
    SEARCH_EXHAUSTED: ReasonCategory
    VERIFY_FAILED: ReasonCategory
    RESOURCE_LIMIT: ReasonCategory
    COST_REJECTED: ReasonCategory
    INTERNAL_INVARIANT: ReasonCategory
    BEST_REWRITE_PROMOTED: ReasonCategory

@final
class ReasonDomain:
    ORCHESTRATOR: ReasonDomain
    SEMILINEAR: ReasonDomain
    SIGNATURE: ReasonDomain
    STRUCTURAL_TRANSFORM: ReasonDomain
    DECOMPOSITION: ReasonDomain
    TEMPLATE_DECOMPOSER: ReasonDomain
    WEIGHTED_POLY_FIT: ReasonDomain
    MULTIVAR_POLY: ReasonDomain
    POLYNOMIAL_RECOVERY: ReasonDomain
    BITWISE_DECOMPOSER: ReasonDomain
    HYBRID_DECOMPOSER: ReasonDomain
    GHOST_RESIDUAL: ReasonDomain
    OPERAND_SIMPLIFIER: ReasonDomain
    LIFTING: ReasonDomain
    VERIFIER: ReasonDomain

class StructuralFlags(enum.IntFlag):
    """Structural shapes the classifier found in an expression."""

    HAS_BITWISE = 1
    HAS_ARITHMETIC = 2
    HAS_MUL = 4
    HAS_MULTILINEAR_PRODUCT = 8
    HAS_SINGLETON_POWER = 16
    HAS_SINGLETON_POWER_GT2 = 32
    HAS_MIXED_PRODUCT = 64
    HAS_BITWISE_OVER_ARITH = 128
    HAS_ARITH_OVER_BITWISE = 256
    HAS_MULTIVAR_HIGH_POWER = 512
    HAS_UNKNOWN_SHAPE = 1024
    # A composite of three flags rather than a bit of its own, so it is a
    # plain attribute rather than a member.
    UNSUPPORTED_MASK: int

class CobraError(Exception):
    code: Union[ErrorCode, None]
    message: str

class InvalidArgumentError(CobraError, ValueError): ...
class ParseError(CobraError, ValueError): ...
class TooManyVariablesError(CobraError, ValueError): ...
class NonLinearInputError(CobraError): ...
class NoReductionError(CobraError): ...
class VerificationFailedError(CobraError): ...
class SimplificationError(CobraError): ...

@final
class Options:
    def __new__(
        cls,
        bitwidth: int = 64,
        max_vars: int = 16,
        spot_check: bool = True,
        enable_bitwise_decomposition: bool = True,
        structural_flags: int = 0,
        require_lean_certificate: bool = True,
    ) -> Options: ...
    @property
    def bitwidth(self) -> int: ...
    @property
    def max_vars(self) -> int: ...
    @property
    def spot_check(self) -> bool: ...
    @property
    def enable_bitwise_decomposition(self) -> bool: ...
    @property
    def structural_flags(self) -> StructuralFlags: ...
    @property
    def require_lean_certificate(self) -> bool: ...
    def __eq__(self, other: object, /) -> bool: ...

@final
class Expr:
    @staticmethod
    def parse(text: str, bitwidth: int = 64) -> Expr: ...
    @staticmethod
    def var(name: str, width: int = 64) -> Expr: ...
    @staticmethod
    def const(value: int, width: int = 64) -> Expr: ...
    @staticmethod
    def concat(high: Expr, low: Expr) -> Expr: ...
    @staticmethod
    def from_dict(state: dict[str, Any]) -> Expr: ...
    @property
    def variables(self) -> list[str]: ...
    @property
    def variable_widths(self) -> list[int]: ...
    @property
    def bitwidth(self) -> int: ...
    @property
    def width(self) -> int: ...
    @property
    def kind(self) -> Kind: ...
    @property
    def children(self) -> list[Expr]: ...
    @property
    def value(self) -> Union[int, None]: ...
    @property
    def variable_index(self) -> Union[int, None]: ...
    @property
    def variable_name(self) -> Union[str, None]: ...
    @property
    def shift_amount(self) -> Union[int, None]: ...
    @property
    def target_width(self) -> Union[int, None]: ...
    def render(self) -> str: ...
    def zext(self, width: int) -> Expr: ...
    def sext(self, width: int) -> Expr: ...
    def trunc(self, width: int) -> Expr: ...
    def evaluate(
        self,
        values: Union[Mapping[str, int], Sequence[int], None] = None,
        **kwargs: int,
    ) -> int: ...
    @overload
    def evaluate_many(
        self,
        values: Union[Mapping[str, _Column], Sequence[_Column]],
        raw: Literal[False] = False,
    ) -> list[int]: ...
    @overload
    def evaluate_many(
        self,
        values: Union[Mapping[str, _Column], Sequence[_Column]],
        raw: Literal[True],
    ) -> bytes: ...
    def signature(self) -> list[int]: ...
    def simplify(self, options: Union[Options, None] = None) -> SimplifyResult: ...
    def to_dict(self) -> dict[str, Any]: ...
    def __str__(self) -> str: ...
    def __eq__(self, other: object, /) -> bool: ...
    def __hash__(self) -> int: ...
    def __reduce__(self) -> tuple[Any, ...]: ...
    def __add__(self, other: Union[Expr, int]) -> Expr: ...
    def __radd__(self, other: Union[Expr, int]) -> Expr: ...
    def __sub__(self, other: Union[Expr, int]) -> Expr: ...
    def __rsub__(self, other: Union[Expr, int]) -> Expr: ...
    def __mul__(self, other: Union[Expr, int]) -> Expr: ...
    def __rmul__(self, other: Union[Expr, int]) -> Expr: ...
    def __and__(self, other: Union[Expr, int]) -> Expr: ...
    def __rand__(self, other: Union[Expr, int]) -> Expr: ...
    def __or__(self, other: Union[Expr, int]) -> Expr: ...
    def __ror__(self, other: Union[Expr, int]) -> Expr: ...
    def __xor__(self, other: Union[Expr, int]) -> Expr: ...
    def __rxor__(self, other: Union[Expr, int]) -> Expr: ...
    def __neg__(self) -> Expr: ...
    def __pos__(self) -> Expr: ...
    def __invert__(self) -> Expr: ...
    def __rshift__(self, amount: int) -> Expr: ...
    def __lshift__(self, amount: int) -> Expr: ...
    def __pow__(self, exponent: int, modulo: None = None) -> Expr: ...

@final
class Telemetry:
    @property
    def total_expansions(self) -> int: ...
    @property
    def max_depth_reached(self) -> int: ...
    @property
    def candidates_verified(self) -> int: ...
    @property
    def queue_high_water(self) -> int: ...

@final
class ReasonCode:
    @property
    def category(self) -> ReasonCategory: ...
    @property
    def domain(self) -> ReasonDomain: ...
    @property
    def subcode(self) -> int: ...
    def __eq__(self, other: object, /) -> bool: ...

@final
class ReasonFrame:
    @property
    def code(self) -> ReasonCode: ...
    @property
    def message(self) -> str: ...
    @property
    def fields(self) -> tuple[tuple[str, str], ...]: ...

@final
class Diagnostic:
    @property
    def semantic_class(self) -> SemanticClass: ...
    @property
    def structural_flags(self) -> StructuralFlags: ...
    @property
    def structural_transform_rounds(self) -> int: ...
    @property
    def transform_produced_candidate(self) -> bool: ...
    @property
    def candidate_failed_verification(self) -> bool: ...
    @property
    def reason(self) -> str: ...
    @property
    def reason_code(self) -> Union[ReasonCode, None]: ...
    @property
    def cause_chain(self) -> tuple[ReasonFrame, ...]: ...

@final
class SimplifyResult:
    @property
    def kind(self) -> OutcomeKind: ...
    @property
    def simplified(self) -> bool: ...
    @property
    def expr(self) -> Union[Expr, None]: ...
    @property
    def original(self) -> Expr: ...
    @property
    def variables(self) -> list[str]: ...
    @property
    def signature(self) -> list[int]: ...
    @property
    def verified(self) -> bool: ...
    @property
    def proof_level(self) -> ProofLevel: ...
    @property
    def diagnostic(self) -> Diagnostic: ...
    @property
    def telemetry(self) -> Telemetry: ...
    def raise_for_error(self) -> None: ...
    def __str__(self) -> str: ...

@overload
def simplify_many(
    expressions: Iterable[Union[str, Expr]],
    options: Union[Options, None] = None,
    workers: Union[int, None] = None,
    on_error: Literal['raise'] = 'raise',
) -> list[SimplifyResult]: ...
@overload
def simplify_many(
    expressions: Iterable[Union[str, Expr]],
    options: Union[Options, None],
    workers: Union[int, None],
    on_error: Literal['none'],
) -> list[Union[SimplifyResult, None]]: ...
def simplify_signature(
    signature: Sequence[int],
    variables: Sequence[str],
    options: Union[Options, None] = None,
) -> SimplifyResult: ...
def build_info() -> dict[str, Any]: ...
