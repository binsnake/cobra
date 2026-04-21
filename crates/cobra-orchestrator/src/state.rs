//! [`StateData`] and its payload variants. Ported from the "payload
//! types" section of `lib/core/Orchestrator.h`.
//!
//! Every payload is a Rust port of the corresponding C++ struct with
//! identical field order. `StateData::kind()` returns the
//! [`StateKind`] discriminator used by the scheduler.

use cobra_core::classification::Classification;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::ExprCost;
use cobra_ir::semilinear::SemilinearIR;

use crate::continuation::GroupId;
use crate::enums::{PassId, Provenance, RemainderOrigin, StateKind};
use crate::stubs::{EliminationResult, ExtractorKind};

// ----- AST / solve context -----

/// Per-subproblem solve context carried alongside an AST payload when
/// the subproblem lives in a reduced variable space.
#[derive(Clone, Debug, Default)]
pub struct AstSolveContext {
    pub vars: Vec<String>,
    pub evaluator: Option<Evaluator>,
    pub input_sig: Vec<u64>,
}

#[derive(Clone, Debug)]
pub struct AstPayload {
    pub expr: Box<Expr>,
    pub classification: Option<Classification>,
    pub provenance: Provenance,
    pub solve_ctx: Option<AstSolveContext>,
}

// ----- Signature-based subproblem -----

#[derive(Clone, Debug, Default)]
pub struct SignatureSubproblemContext {
    pub sig: Vec<u64>,
    pub real_vars: Vec<String>,
    pub elimination: EliminationResult,
    pub original_indices: Vec<u32>,
    pub needs_original_space_verification: bool,
}

#[derive(Clone, Debug, Default)]
pub struct SignatureStatePayload {
    pub ctx: SignatureSubproblemContext,
}

#[derive(Clone, Debug, Default)]
pub struct SignatureCoeffStatePayload {
    pub ctx: SignatureSubproblemContext,
    pub coeffs: Vec<u64>,
}

// ----- Candidate (verified / unverified simplified expression) -----

#[derive(Clone, Debug)]
pub struct CandidatePayload {
    pub expr: Box<Expr>,
    pub real_vars: Vec<String>,
    pub cost: ExprCost,
    pub producing_pass: PassId,
    pub needs_original_space_verification: bool,
}

// ----- Core + remainder state (decomposition family) -----

/// Target-local context used when a decomposition is solved in a
/// smaller variable space than the parent expression.
#[derive(Clone, Debug, Default)]
pub struct RemainderTargetContext {
    pub eval: Evaluator,
    pub vars: Vec<String>,
    pub remap_support: Vec<u32>,
}

#[derive(Clone, Debug)]
pub struct CoreCandidatePayload {
    pub core_expr: Box<Expr>,
    pub extractor_kind: ExtractorKind,
    pub degree_used: u8,
    pub source_sig: Vec<u64>,
    pub target: RemainderTargetContext,
}

#[derive(Clone, Debug)]
pub struct RemainderStatePayload {
    pub origin: RemainderOrigin,
    pub prefix_expr: Box<Expr>,
    pub prefix_degree: u8,
    pub remainder_eval: Evaluator,
    pub source_sig: Vec<u64>,
    pub remainder_sig: Vec<u64>,
    pub remainder_elim: EliminationResult,
    pub remainder_support: Vec<u32>,
    pub is_boolean_null: bool,
    pub degree_floor: u8,
    pub target: RemainderTargetContext,
}

// ----- Lifting -----

#[derive(Clone, Debug)]
pub struct LiftedSkeletonPayload {
    pub outer_expr: Box<Expr>,
    pub outer_ctx: AstSolveContext,
    pub bindings: Vec<crate::continuation::LiftedBinding>,
    pub original_var_count: u32,
    pub baseline_cost: ExprCost,
    pub source_sig: Vec<u64>,
    /// Parent-local context — nested lifting must resolve back into
    /// this space, not necessarily the global original space.
    pub original_ctx: AstSolveContext,
}

// ----- Semilinear pipeline -----

#[derive(Clone, Debug, Default)]
pub struct SemilinearContext {
    pub ir: SemilinearIR,
    pub vars: Vec<String>,
    pub evaluator: Option<Evaluator>,
}

#[derive(Clone, Debug, Default)]
pub struct NormalizedSemilinearPayload {
    pub ctx: SemilinearContext,
}

#[derive(Clone, Debug, Default)]
pub struct CheckedSemilinearPayload {
    pub ctx: SemilinearContext,
}

#[derive(Clone, Debug, Default)]
pub struct RewrittenSemilinearPayload {
    pub ctx: SemilinearContext,
}

// ----- Competition resolution -----

#[derive(Copy, Clone, Debug, Default)]
pub struct CompetitionResolvedPayload {
    pub group_id: GroupId,
}

// ----- Umbrella -----

/// Tagged union over every payload type. Matches C++ `StateData` variant
/// order — the index of each arm equals the `StateKind` discriminator's
/// numeric value, so fingerprinting and scheduling can switch on
/// `kind()` without touching the payload.
#[derive(Clone, Debug)]
pub enum StateData {
    FoldedAst(Box<AstPayload>),
    Signature(Box<SignatureStatePayload>),
    SignatureCoeff(Box<SignatureCoeffStatePayload>),
    CoreCandidate(Box<CoreCandidatePayload>),
    Remainder(Box<RemainderStatePayload>),
    SemilinearNormalized(Box<NormalizedSemilinearPayload>),
    SemilinearChecked(Box<CheckedSemilinearPayload>),
    SemilinearRewritten(Box<RewrittenSemilinearPayload>),
    LiftedSkeleton(Box<LiftedSkeletonPayload>),
    Candidate(Box<CandidatePayload>),
    CompetitionResolved(CompetitionResolvedPayload),
}

impl StateData {
    #[inline]
    #[must_use]
    pub fn kind(&self) -> StateKind {
        match self {
            Self::FoldedAst(_) => StateKind::FoldedAst,
            Self::Signature(_) => StateKind::SignatureState,
            Self::SignatureCoeff(_) => StateKind::SignatureCoeffState,
            Self::CoreCandidate(_) => StateKind::CoreCandidate,
            Self::Remainder(_) => StateKind::RemainderState,
            Self::SemilinearNormalized(_) => StateKind::SemilinearNormalizedIr,
            Self::SemilinearChecked(_) => StateKind::SemilinearCheckedIr,
            Self::SemilinearRewritten(_) => StateKind::SemilinearRewrittenIr,
            Self::LiftedSkeleton(_) => StateKind::LiftedSkeleton,
            Self::Candidate(_) => StateKind::CandidateExpr,
            Self::CompetitionResolved(_) => StateKind::CompetitionResolved,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kind_round_trip_for_every_variant() {
        // One smoke-construction per StateData arm, all paired with the
        // expected StateKind discriminator. Exercising every arm here
        // guarantees the `kind()` match stays exhaustive as the enum
        // evolves.
        let ast = StateData::FoldedAst(Box::new(AstPayload {
            expr: Expr::variable(0),
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        }));
        assert_eq!(ast.kind(), StateKind::FoldedAst);

        let sig: StateData = StateData::Signature(Box::default());
        assert_eq!(sig.kind(), StateKind::SignatureState);

        let sig_c: StateData = StateData::SignatureCoeff(Box::default());
        assert_eq!(sig_c.kind(), StateKind::SignatureCoeffState);

        let core = StateData::CoreCandidate(Box::new(CoreCandidatePayload {
            core_expr: Expr::variable(0),
            extractor_kind: ExtractorKind::Polynomial,
            degree_used: 0,
            source_sig: vec![],
            target: RemainderTargetContext::default(),
        }));
        assert_eq!(core.kind(), StateKind::CoreCandidate);

        let rem = StateData::Remainder(Box::new(RemainderStatePayload {
            origin: RemainderOrigin::ProductCore,
            prefix_expr: Expr::variable(0),
            prefix_degree: 0,
            remainder_eval: Evaluator::default(),
            source_sig: vec![],
            remainder_sig: vec![],
            remainder_elim: EliminationResult::default(),
            remainder_support: vec![],
            is_boolean_null: false,
            degree_floor: 2,
            target: RemainderTargetContext::default(),
        }));
        assert_eq!(rem.kind(), StateKind::RemainderState);

        let sn: StateData = StateData::SemilinearNormalized(Box::default());
        assert_eq!(sn.kind(), StateKind::SemilinearNormalizedIr);

        let sc: StateData = StateData::SemilinearChecked(Box::default());
        assert_eq!(sc.kind(), StateKind::SemilinearCheckedIr);

        let sr: StateData = StateData::SemilinearRewritten(Box::default());
        assert_eq!(sr.kind(), StateKind::SemilinearRewrittenIr);

        let lifted = StateData::LiftedSkeleton(Box::new(LiftedSkeletonPayload {
            outer_expr: Expr::variable(0),
            outer_ctx: AstSolveContext::default(),
            bindings: vec![],
            original_var_count: 0,
            baseline_cost: ExprCost::default(),
            source_sig: vec![],
            original_ctx: AstSolveContext::default(),
        }));
        assert_eq!(lifted.kind(), StateKind::LiftedSkeleton);

        let cand = StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: vec![],
            cost: ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: true,
        }));
        assert_eq!(cand.kind(), StateKind::CandidateExpr);

        let resolved = StateData::CompetitionResolved(CompetitionResolvedPayload { group_id: 7 });
        assert_eq!(resolved.kind(), StateKind::CompetitionResolved);
    }
}
