//! Shared helper: combine a solved residual expression with the
//! remainder's prefix, verify at full width, and emit a candidate.

use cobra_core::classification::Classification;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::pass_contract::{DecompositionMeta, VerificationState};

use cobra_orchestrator::{
    project_extractor_kind, CandidatePayload, ItemDisposition, OrchestratorContext, PassDecision,
    PassId, PassResult, RemainderStatePayload, ResidualSolverKind, StateData, WorkItem,
};

use crate::bitwise_decomposer::remap_vars;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

/// Emit a candidate by combining `residual.prefix_expr` with the
/// caller's `solved_expr`. Returns `None` when the full-width check
pub fn try_recombine_and_emit(
    residual: &RemainderStatePayload,
    mut solved_expr: Box<Expr>,
    solved_expr_vars: &[String],
    parent: &WorkItem,
    ctx: &OrchestratorContext,
    producing_pass: PassId,
    solver_kind: ResidualSolverKind,
) -> Option<PassResult> {
    let target_vars: Vec<String> = if residual.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        residual.target.vars.clone()
    };
    let target_eval = if residual.target.vars.is_empty() {
        ctx.evaluator.clone()?
    } else {
        residual.target.eval.clone()
    };
    let remap = if residual.target.remap_support.is_empty() {
        residual.remainder_support.clone()
    } else {
        residual.target.remap_support.clone()
    };

    // When the solver's expression lives in a reduced variable space,
    // remap its indices into the target space.
    if solved_expr_vars.len() < target_vars.len() && !remap.is_empty() {
        solved_expr = remap_vars(&solved_expr, &remap);
    }

    let combined = {
        let prefix_is_zero = matches!(
            residual.prefix_expr.kind,
            cobra_core::expr::Kind::Constant(0)
        );
        if prefix_is_zero {
            solved_expr
        } else {
            Expr::add(residual.prefix_expr.clone_tree(), solved_expr)
        }
    };

    let num_vars = target_vars.len() as u32;
    let check = full_width_check_eval(
        &target_eval,
        num_vars,
        &combined,
        ctx.bitwidth,
        DEFAULT_NUM_SAMPLES,
    );
    if !check.passed {
        return None;
    }

    let cost_info = compute_cost(&combined);
    let mut cand_item = parent.clone();
    cand_item.payload = StateData::Candidate(Box::new(CandidatePayload {
        expr: combined,
        real_vars: target_vars,
        cost: cost_info.cost,
        producing_pass,
        needs_original_space_verification: false,
    }));
    cand_item.metadata.verification = VerificationState::Verified;
    cand_item
        .metadata
        .sig_vector
        .clone_from(&residual.source_sig);
    cand_item.metadata.decomposition_meta = Some(DecompositionMeta {
        extractor_kind: project_extractor_kind(residual.origin) as u8,
        solver_kind: solver_kind as u8,
        has_solver: true,
        core_degree: residual.prefix_degree,
    });

    Some(PassResult {
        decision: PassDecision::SolvedCandidate,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![cand_item],
        reason: cobra_core::pass_contract::ReasonDetail::default(),
    })
}

/// are compiled.
#[doc(hidden)]
#[must_use]
pub fn _classification_anchor() -> Classification {
    Classification::default()
}
