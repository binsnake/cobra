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
use crate::candidate_normalize::signature_certificate_for_candidate;
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
    let lean_signature_certificate = signature_certificate_for_candidate(
        ctx.bitwidth,
        &residual.source_sig,
        &target_vars,
        &combined,
    );
    let mut cand_item = parent.clone();
    cand_item.payload = StateData::Candidate(Box::new(CandidatePayload {
        expr: combined,
        real_vars: target_vars.clone(),
        cost: cost_info.cost,
        producing_pass,
        needs_original_space_verification: false,
    }));
    cand_item.metadata.verification = VerificationState::Verified;
    cand_item
        .metadata
        .sig_vector
        .clone_from(&residual.source_sig);
    cand_item.metadata.lean_certificate = None;
    cand_item.metadata.lean_signature_certificate = lean_signature_certificate;
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

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{RemainderOrigin, RemainderTargetContext};

    #[test]
    fn recombine_attaches_source_signature_certificate() {
        let vars = vec!["x".to_owned()];
        let expr = Expr::variable(0);
        let eval = Evaluator::from_expr(&expr, 64);
        let residual = RemainderStatePayload {
            origin: RemainderOrigin::PolynomialCore,
            prefix_expr: Expr::constant(0),
            prefix_degree: 0,
            remainder_eval: eval.clone(),
            source_sig: vec![0, 1],
            remainder_sig: vec![0, 1],
            remainder_elim: cobra_orchestrator::EliminationResult::default(),
            remainder_support: vec![0],
            is_boolean_null: false,
            degree_floor: 0,
            target: RemainderTargetContext {
                eval,
                vars: vars.clone(),
                remap_support: Vec::new(),
            },
        };
        let parent = WorkItem::new(StateData::Remainder(Box::new(residual.clone())));
        let ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);

        let pr = try_recombine_and_emit(
            &residual,
            Expr::variable(0),
            &vars,
            &parent,
            &ctx,
            PassId::ResidualPolyRecovery,
            ResidualSolverKind::PolynomialRecovery,
        )
        .expect("recombine succeeds");

        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        let cert = pr.next[0]
            .metadata
            .lean_signature_certificate
            .as_ref()
            .expect("recombined candidate has source signature certificate");
        assert!(cert.matches_signature(64, 1, &[0, 1], cert.expr.as_ref()));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
    }
}
