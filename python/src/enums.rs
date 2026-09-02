//! Python enums mirroring the library's plain Rust enums.
//!
//! Variant names are spelled the way Python spells constants, so callers
//! write `Kind.ADD` and `ProofLevel.LEAN_CERTIFIED`.

use cobra::core::classification::SemanticClass;
use cobra::core::pass_contract::{ReasonCategory, ReasonDomain};
use cobra::{CobraError, Kind, ProofLevel, SimplifyOutcomeKind};
use pyo3::prelude::*;

/// Which library error a `CobraError` exception carries.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "ErrorCode",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyErrorCode {
    #[pyo3(name = "INVALID_ARGUMENT")]
    InvalidArgument,
    #[pyo3(name = "PARSE_ERROR")]
    ParseError,
    #[pyo3(name = "NON_LINEAR_INPUT")]
    NonLinearInput,
    #[pyo3(name = "TOO_MANY_VARIABLES")]
    TooManyVariables,
    #[pyo3(name = "NO_REDUCTION")]
    NoReduction,
    #[pyo3(name = "VERIFICATION_FAILED")]
    VerificationFailed,
}

impl From<CobraError> for PyErrorCode {
    fn from(code: CobraError) -> Self {
        match code {
            CobraError::InvalidArgument => Self::InvalidArgument,
            CobraError::ParseError => Self::ParseError,
            CobraError::NonLinearInput => Self::NonLinearInput,
            CobraError::TooManyVariables => Self::TooManyVariables,
            CobraError::NoReduction => Self::NoReduction,
            CobraError::VerificationFailed => Self::VerificationFailed,
        }
    }
}

/// Expression node kind. Payloads live on `Expr` properties: `value`,
/// `variable_index`, `shift_amount`, and `target_width`.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "Kind",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyKind {
    #[pyo3(name = "CONSTANT")]
    Constant,
    #[pyo3(name = "VARIABLE")]
    Variable,
    #[pyo3(name = "ADD")]
    Add,
    #[pyo3(name = "MUL")]
    Mul,
    #[pyo3(name = "AND")]
    And,
    #[pyo3(name = "OR")]
    Or,
    #[pyo3(name = "XOR")]
    Xor,
    #[pyo3(name = "NOT")]
    Not,
    #[pyo3(name = "NEG")]
    Neg,
    #[pyo3(name = "SHR")]
    Shr,
    #[pyo3(name = "ZEXT")]
    ZExt,
    #[pyo3(name = "SEXT")]
    SExt,
    #[pyo3(name = "TRUNC")]
    Trunc,
    #[pyo3(name = "CONCAT")]
    Concat,
}

impl From<&Kind> for PyKind {
    fn from(kind: &Kind) -> Self {
        match kind {
            Kind::Constant(_) => Self::Constant,
            Kind::Variable(_) => Self::Variable,
            Kind::Add => Self::Add,
            Kind::Mul => Self::Mul,
            Kind::And => Self::And,
            Kind::Or => Self::Or,
            Kind::Xor => Self::Xor,
            Kind::Not => Self::Not,
            Kind::Neg => Self::Neg,
            Kind::Shr(_) => Self::Shr,
            Kind::ZExt(_) => Self::ZExt,
            Kind::SExt(_) => Self::SExt,
            Kind::Trunc(_) => Self::Trunc,
            Kind::Concat => Self::Concat,
        }
    }
}

/// Which of the three arms the pipeline returned.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "OutcomeKind",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyOutcomeKind {
    #[pyo3(name = "SIMPLIFIED")]
    Simplified,
    #[pyo3(name = "UNCHANGED_UNSUPPORTED")]
    UnchangedUnsupported,
    #[pyo3(name = "ERROR")]
    Error,
}

impl From<SimplifyOutcomeKind> for PyOutcomeKind {
    fn from(kind: SimplifyOutcomeKind) -> Self {
        match kind {
            SimplifyOutcomeKind::Simplified => Self::Simplified,
            SimplifyOutcomeKind::UnchangedUnsupported => Self::UnchangedUnsupported,
            SimplifyOutcomeKind::Error => Self::Error,
        }
    }
}

/// Strength of the evidence behind a simplified expression.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "ProofLevel",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyProofLevel {
    #[pyo3(name = "UNVERIFIED")]
    Unverified,
    #[pyo3(name = "SPOT_CHECKED")]
    SpotChecked,
    #[pyo3(name = "SMT_PROVED")]
    SmtProved,
    #[pyo3(name = "LEAN_CERTIFIED")]
    LeanCertified,
}

impl From<ProofLevel> for PyProofLevel {
    fn from(level: ProofLevel) -> Self {
        match level {
            ProofLevel::Unverified => Self::Unverified,
            ProofLevel::SpotChecked => Self::SpotChecked,
            ProofLevel::SmtProved => Self::SmtProved,
            ProofLevel::LeanCertified => Self::LeanCertified,
        }
    }
}

/// Semantic bucket the classifier put the input in.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "SemanticClass",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PySemanticClass {
    #[pyo3(name = "LINEAR")]
    Linear,
    #[pyo3(name = "SEMILINEAR")]
    Semilinear,
    #[pyo3(name = "POLYNOMIAL")]
    Polynomial,
    #[pyo3(name = "NON_POLYNOMIAL")]
    NonPolynomial,
}

impl From<SemanticClass> for PySemanticClass {
    fn from(class: SemanticClass) -> Self {
        match class {
            SemanticClass::Linear => Self::Linear,
            SemanticClass::Semilinear => Self::Semilinear,
            SemanticClass::Polynomial => Self::Polynomial,
            SemanticClass::NonPolynomial => Self::NonPolynomial,
        }
    }
}

/// Why a pass or the orchestrator stopped.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "ReasonCategory",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyReasonCategory {
    #[pyo3(name = "NONE")]
    None,
    #[pyo3(name = "GUARD_FAILED")]
    GuardFailed,
    #[pyo3(name = "INAPPLICABLE")]
    Inapplicable,
    #[pyo3(name = "REPRESENTATION_GAP")]
    RepresentationGap,
    #[pyo3(name = "NO_SOLUTION")]
    NoSolution,
    #[pyo3(name = "SEARCH_EXHAUSTED")]
    SearchExhausted,
    #[pyo3(name = "VERIFY_FAILED")]
    VerifyFailed,
    #[pyo3(name = "RESOURCE_LIMIT")]
    ResourceLimit,
    #[pyo3(name = "COST_REJECTED")]
    CostRejected,
    #[pyo3(name = "INTERNAL_INVARIANT")]
    InternalInvariant,
    #[pyo3(name = "BEST_REWRITE_PROMOTED")]
    BestRewritePromoted,
}

impl From<ReasonCategory> for PyReasonCategory {
    fn from(category: ReasonCategory) -> Self {
        match category {
            ReasonCategory::None => Self::None,
            ReasonCategory::GuardFailed => Self::GuardFailed,
            ReasonCategory::Inapplicable => Self::Inapplicable,
            ReasonCategory::RepresentationGap => Self::RepresentationGap,
            ReasonCategory::NoSolution => Self::NoSolution,
            ReasonCategory::SearchExhausted => Self::SearchExhausted,
            ReasonCategory::VerifyFailed => Self::VerifyFailed,
            ReasonCategory::ResourceLimit => Self::ResourceLimit,
            ReasonCategory::CostRejected => Self::CostRejected,
            ReasonCategory::InternalInvariant => Self::InternalInvariant,
            ReasonCategory::BestRewritePromoted => Self::BestRewritePromoted,
        }
    }
}

/// Which part of the pipeline produced a reason frame.
#[pyclass(
    eq,
    eq_int,
    frozen,
    hash,
    from_py_object,
    name = "ReasonDomain",
    module = "cobra_mba"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PyReasonDomain {
    #[pyo3(name = "ORCHESTRATOR")]
    Orchestrator,
    #[pyo3(name = "SEMILINEAR")]
    Semilinear,
    #[pyo3(name = "SIGNATURE")]
    Signature,
    #[pyo3(name = "STRUCTURAL_TRANSFORM")]
    StructuralTransform,
    #[pyo3(name = "DECOMPOSITION")]
    Decomposition,
    #[pyo3(name = "TEMPLATE_DECOMPOSER")]
    TemplateDecomposer,
    #[pyo3(name = "WEIGHTED_POLY_FIT")]
    WeightedPolyFit,
    #[pyo3(name = "MULTIVAR_POLY")]
    MultivarPoly,
    #[pyo3(name = "POLYNOMIAL_RECOVERY")]
    PolynomialRecovery,
    #[pyo3(name = "BITWISE_DECOMPOSER")]
    BitwiseDecomposer,
    #[pyo3(name = "HYBRID_DECOMPOSER")]
    HybridDecomposer,
    #[pyo3(name = "GHOST_RESIDUAL")]
    GhostResidual,
    #[pyo3(name = "OPERAND_SIMPLIFIER")]
    OperandSimplifier,
    #[pyo3(name = "LIFTING")]
    Lifting,
    #[pyo3(name = "VERIFIER")]
    Verifier,
}

impl From<ReasonDomain> for PyReasonDomain {
    fn from(domain: ReasonDomain) -> Self {
        match domain {
            ReasonDomain::Orchestrator => Self::Orchestrator,
            ReasonDomain::Semilinear => Self::Semilinear,
            ReasonDomain::Signature => Self::Signature,
            ReasonDomain::StructuralTransform => Self::StructuralTransform,
            ReasonDomain::Decomposition => Self::Decomposition,
            ReasonDomain::TemplateDecomposer => Self::TemplateDecomposer,
            ReasonDomain::WeightedPolyFit => Self::WeightedPolyFit,
            ReasonDomain::MultivarPoly => Self::MultivarPoly,
            ReasonDomain::PolynomialRecovery => Self::PolynomialRecovery,
            ReasonDomain::BitwiseDecomposer => Self::BitwiseDecomposer,
            ReasonDomain::HybridDecomposer => Self::HybridDecomposer,
            ReasonDomain::GhostResidual => Self::GhostResidual,
            ReasonDomain::OperandSimplifier => Self::OperandSimplifier,
            ReasonDomain::Lifting => Self::Lifting,
            ReasonDomain::Verifier => Self::Verifier,
        }
    }
}

/// Register every enum on the extension module.
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyErrorCode>()?;
    m.add_class::<PyKind>()?;
    m.add_class::<PyOutcomeKind>()?;
    m.add_class::<PyProofLevel>()?;
    m.add_class::<PySemanticClass>()?;
    m.add_class::<PyReasonCategory>()?;
    m.add_class::<PyReasonDomain>()?;
    Ok(())
}
