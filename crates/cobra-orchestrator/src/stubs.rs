//! Forward-declared types from pass-adjacent modules that haven't been
//! ported yet. Each stub is kept at the exact shape the orchestrator
//! needs to carry in `StateData` / `ContinuationData` / `JoinState`.
//! When the owning pass is ported, these move out into their respective
//! `cobra-passes::*` submodule and this file shrinks.

// ----- AuxVarEliminator -----

/// Ported from `include/cobra/core/AuxVarEliminator.h`. The full
/// elimination function lives in the signature-pass family; the
/// orchestrator only carries the result struct in work-item payloads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EliminationResult {
    pub reduced_sig: Vec<u64>,
    pub real_vars: Vec<String>,
    pub spurious_vars: Vec<String>,
}

// ----- DecompositionEngine -----

/// Which extractor produced a `CoreCandidate` / `Remainder` pair.
/// Matches C++ `ExtractorKind`. `#[repr(u8)]` so `DecompositionMeta`
/// can store its bit pattern without losing parity.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ExtractorKind {
    ProductAst,
    Polynomial,
    Template,
    #[default]
    BooleanNullDirect,
}

/// Which solver finishes a decomposition residual. Matches C++
/// `ResidualSolverKind`.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ResidualSolverKind {
    #[default]
    SupportedPipeline,
    PolynomialRecovery,
    GhostResidual,
    TemplateDecomposition,
}

// ----- BitwiseDecomposer -----

/// Gate kinds the bitwise decomposer considers when trying to fit the
/// signature into a `g(...) + k*(...)` shape. Matches C++ `GateKind`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum GateKind {
    And,
    Or,
    Xor,
    Mul,
    Add,
}

// ----- HybridDecomposer -----

/// Invertible operator the hybrid decomposer strips from the outside.
/// Matches C++ `ExtractOp`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExtractOp {
    Xor,
    Add,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_enums_have_expected_defaults() {
        assert_eq!(ExtractorKind::default(), ExtractorKind::BooleanNullDirect);
        assert_eq!(
            ResidualSolverKind::default(),
            ResidualSolverKind::SupportedPipeline
        );
        assert!(EliminationResult::default().real_vars.is_empty());
    }

    #[test]
    fn repr_u8_enums_compact() {
        // Sanity: these enums need to survive a `#[repr(u8)]` round trip
        // because `DecompositionMeta` stores them as raw u8.
        assert_eq!(std::mem::size_of::<ExtractorKind>(), 1);
        assert_eq!(std::mem::size_of::<ResidualSolverKind>(), 1);
    }
}
