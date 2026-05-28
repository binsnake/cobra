//! Core enumerations used throughout the orchestrator. Each is a direct
//! that numeric casts (used in places like `DecompositionMeta`) stay
//! bit-compatible.

// ----- State machine -----

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum StateKind {
    FoldedAst,
    SignatureState,
    SignatureCoeffState,
    CoreCandidate,
    RemainderState,
    SemilinearNormalizedIr,
    SemilinearCheckedIr,
    SemilinearRewrittenIr,
    LiftedSkeleton,
    CandidateExpr,
    CompetitionResolved,
}

/// `Provenance`.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum Provenance {
    #[default]
    Original,
    Lowered,
    Rewritten,
}

/// `PassDecision`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PassDecision {
    NotApplicable,
    NoProgress,
    Advance,
    SolvedCandidate,
    Blocked,
}

/// What the orchestrator should do with the work item after the pass
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum ItemDisposition {
    RetainCurrent,
    ReplaceCurrent,
    #[default]
    ConsumeCurrent,
}

/// `RemainderOrigin` (sized `u8`).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum RemainderOrigin {
    #[default]
    DirectBooleanNull,
    ProductCore,
    PolynomialCore,
    TemplateCore,
    SignatureLowering,
    LiftedOuter,
}

// ----- Pass identity -----

/// stores per-item `attempted_mask` as a `u64` bitset, so any addition
/// here must keep `Count_ <= 64`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum PassId {
    LowerNotOverArith,
    ClassifyAst,
    BuildSignatureState,
    // Semilinear passes
    SemilinearNormalize,
    SemilinearCheck,
    SemilinearRewrite,
    SemilinearReconstruct,
    // Decomposition extractors
    ExtractProductCore,
    ExtractPolyCoreD2,
    ExtractTemplateCore,
    ExtractPolyCoreD3,
    ExtractPolyCoreD4,
    // Remainder prep
    PrepareDirectRemainder,
    PrepareRemainderFromCore,
    // Decomposition residual solvers
    ResidualSupported,
    ResidualPolyRecovery,
    ResidualGhost,
    ResidualFactoredGhost,
    ResidualFactoredGhostEscalated,
    ResidualTemplate,
    // Competition resolution
    ResolveCompetition,
    // Signature technique passes
    SignaturePatternMatch,
    SignatureAnf,
    PrepareCoeffModel,
    SignatureCobCandidate,
    SignatureSingletonPolyRecovery,
    SignatureMultivarPolyRecovery,
    SignatureBitwiseDecompose,
    SignatureHybridDecompose,
    // Structural rewrites
    OperandSimplify,
    ProductIdentityCollapse,
    XorLowering,
    VerifyCandidate,
    // Lifting passes
    LiftArithmeticAtoms,
    LiftRepeatedSubexpressions,
    PrepareLiftedOuterSolve,
    // Pseudo-pass used as a history marker. `SeedWithAst` stamps it
    // when `simplify_pattern_subtrees` rewrote the input during
    // seeding, so the main loop's exhaustion-path fallback can
    // recognise the seed tree as a cost-improving rewrite and promote
    // it if the downstream pipeline can't terminate.
    PatternSubtreeRewrite,
    // Runtime pass that applies closed-form bitwise identities over
    // arbitrary atoms (e.g. `(A|B) - (A&B) -> A^B`).
    AtomIdentityRewrite,
}

impl PassId {
    /// Number of `PassId` variants. Kept separate from `std::mem::variant_count`
    /// (which is still nightly) so this stays on stable.
    pub const COUNT: u8 = 38;

    /// Cast to `u8` — used as the bit position in `attempted_mask`.
    #[inline]
    #[must_use]
    pub fn as_u8(self) -> u8 {
        self as u8
    }

    /// `IsDecompositionFamilyPass`: `ExtractProductCore .. ResidualTemplate`
    /// (inclusive).
    #[inline]
    #[must_use]
    pub fn is_decomposition_family(self) -> bool {
        let v = self.as_u8();
        v >= Self::ExtractProductCore.as_u8() && v <= Self::ResidualTemplate.as_u8()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PassTag {
    Analysis,
    Rewrite,
    Solver,
    Verifier,
}

// ----- Remainder → extractor projection -----

use crate::stubs::ExtractorKind;

#[inline]
#[must_use]
pub fn project_extractor_kind(origin: RemainderOrigin) -> ExtractorKind {
    match origin {
        RemainderOrigin::DirectBooleanNull
        | RemainderOrigin::SignatureLowering
        | RemainderOrigin::LiftedOuter => ExtractorKind::BooleanNullDirect,
        RemainderOrigin::ProductCore => ExtractorKind::ProductAst,
        RemainderOrigin::PolynomialCore => ExtractorKind::Polynomial,
        RemainderOrigin::TemplateCore => ExtractorKind::Template,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pass_id_fits_in_bitmask_budget() {
        // `attempted_mask: u64` — we have headroom up to 64 variants.
        const _: () = assert!(PassId::COUNT <= 64);
        assert_eq!(PassId::AtomIdentityRewrite.as_u8(), PassId::COUNT - 1);
    }

    #[test]
    fn decomposition_family_span() {
        assert!(PassId::ExtractProductCore.is_decomposition_family());
        assert!(PassId::ResidualTemplate.is_decomposition_family());
        assert!(!PassId::ClassifyAst.is_decomposition_family());
        assert!(!PassId::ResolveCompetition.is_decomposition_family());
    }

    #[test]
    fn project_extractor_kind_matches_cpp() {
        assert_eq!(
            project_extractor_kind(RemainderOrigin::ProductCore),
            ExtractorKind::ProductAst
        );
        assert_eq!(
            project_extractor_kind(RemainderOrigin::PolynomialCore),
            ExtractorKind::Polynomial
        );
        assert_eq!(
            project_extractor_kind(RemainderOrigin::TemplateCore),
            ExtractorKind::Template
        );
        // All the "direct" sources collapse to BooleanNullDirect
        for o in [
            RemainderOrigin::DirectBooleanNull,
            RemainderOrigin::SignatureLowering,
            RemainderOrigin::LiftedOuter,
        ] {
            assert_eq!(project_extractor_kind(o), ExtractorKind::BooleanNullDirect);
        }
    }

    #[test]
    fn item_disposition_default_is_consume() {
        assert_eq!(ItemDisposition::default(), ItemDisposition::ConsumeCurrent);
    }
}
