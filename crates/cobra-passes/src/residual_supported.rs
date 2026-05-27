//! `ResidualSupported` pass — recurse into a fresh signature-state
//! solve over the residual, with `evaluator_override` set to the
//! residual evaluator (so child passes verify against the residual,
//! not the original target).
//!
//! On entry: a `Remainder` payload. The pass eliminates auxiliary
//! variables in the target space, opens a competition group with a
//! `RemainderRecombineCont`, acquires a parent-group handle (so the
//! parent does not resolve before this child closes), and emits a
//! `SignatureState` child that the scheduler routes through the
//! signature-pipeline passes.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    acquire_handle, create_group, ContinuationData, ItemDisposition, OrchestratorContext,
    PassDecision, PassResult, RemainderRecombineCont, SignatureStatePayload,
    SignatureSubproblemContext, StateData, WorkItem,
};

use crate::aux_var::eliminate_aux_vars;

const RESIDUAL_FAILED: u16 = 1;

fn residual_failed(msg: &'static str) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::NoSolution,
                domain: ReasonDomain::Decomposition,
                subcode: RESIDUAL_FAILED,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_residual_supported(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::Remainder(residual) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let target_vars: Vec<String> = if residual.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        residual.target.vars.clone()
    };

    let elim = eliminate_aux_vars(&residual.remainder_sig, &target_vars);
    let real_var_count = elim.real_vars.len() as u32;
    if real_var_count == 0 || real_var_count > ctx.opts.max_vars {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: residual_failed("residual variable count out of range"),
        });
    }

    let original_indices =
        cobra_core::expr_rewrite::build_var_support(&target_vars, &elim.real_vars);

    let parent_group_id = item.group_id;
    if let Some(pid) = parent_group_id {
        acquire_handle(&mut ctx.competition_groups, pid);
    }

    let target_eval = if residual.target.vars.is_empty() {
        ctx.evaluator
            .as_ref()
            .expect("ResidualSupported requires a global evaluator when target_vars is empty")
            .clone()
    } else {
        residual.target.eval.clone()
    };

    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    let cont = RemainderRecombineCont {
        prefix_expr: residual.prefix_expr.clone_tree(),
        origin: residual.origin,
        remainder_eval: residual.remainder_eval.clone(),
        source_sig: residual.source_sig.clone(),
        remainder_support: residual.remainder_support.clone(),
        prefix_degree: residual.prefix_degree,
        parent_group_id,
        target_eval,
        target_vars: target_vars.clone(),
    };
    ctx.competition_groups
        .get_mut(&group_id)
        .expect("group just created")
        .continuation = Some(ContinuationData::RemainderRecombine(Box::new(cont)));

    let reduced_sig = elim.reduced_sig.clone();
    let real_vars = elim.real_vars.clone();
    let target_arity = target_vars.len() as u32;
    let mut child = WorkItem::new(StateData::Signature(Box::new(SignatureStatePayload {
        ctx: SignatureSubproblemContext {
            sig: reduced_sig.clone(),
            real_vars,
            elimination: elim,
            original_indices,
            needs_original_space_verification: true,
        },
    })));
    child.features = item.features.clone();
    child.metadata = item.metadata.clone();
    child.metadata.lean_certificate = None;
    child.metadata.lean_signature_certificate = None;
    child.group_id = Some(group_id);
    child.signature_recursion_depth = item.signature_recursion_depth;
    child.evaluator_override = Some(residual.remainder_eval.clone());
    child.evaluator_override_arity = target_arity;

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![child],
        reason: ReasonDetail::default(),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Remainder(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{EliminationResult, RemainderStatePayload, RemainderTargetContext};

    fn mk_remainder_item(
        vars: Vec<String>,
        sig: Vec<u64>,
        prefix: Box<Expr>,
        eval: Evaluator,
    ) -> WorkItem {
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = RemainderStatePayload {
            origin: cobra_orchestrator::RemainderOrigin::DirectBooleanNull,
            prefix_expr: prefix,
            prefix_degree: 0,
            remainder_eval: eval.clone(),
            source_sig: sig.clone(),
            remainder_sig: sig,
            remainder_elim: elim,
            remainder_support: (0..vars.len() as u32).collect(),
            is_boolean_null: false,
            degree_floor: 0,
            target: RemainderTargetContext {
                eval,
                vars,
                remap_support: Vec::new(),
            },
        };
        WorkItem::new(StateData::Remainder(Box::new(payload)))
    }

    #[test]
    fn out_of_range_var_count_blocks() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let zero_sig = vec![0u64; 1]; // one entry, zero vars
        let eval = Evaluator::from_expr(&Expr::constant(0), 64);
        let item = mk_remainder_item(vec![], zero_sig, Expr::constant(0), eval);
        let pr = run_residual_supported(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Blocked);
    }

    #[test]
    fn opens_group_and_emits_signature_child() {
        // 2-var residual that's not aux-var-collapsible (sig depends on both).
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let f = Expr::xor(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&f, 64);
        let sig = vec![0u64, 1, 1, 0];
        let mut item =
            mk_remainder_item(vec!["x".into(), "y".into()], sig, Expr::constant(0), eval);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));

        let pr = run_residual_supported(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        let child = &pr.next[0];
        assert!(matches!(child.payload, StateData::Signature(_)));
        assert!(child.evaluator_override.is_some());
        assert_eq!(child.evaluator_override_arity, 2);
        assert!(child.group_id.is_some());
        // The freshly-created group must hold a RemainderRecombine continuation.
        let gid = child.group_id.unwrap();
        let group = &ctx.competition_groups[&gid];
        assert!(matches!(
            group.continuation,
            Some(ContinuationData::RemainderRecombine(_))
        ));
        assert!(child.metadata.lean_certificate.is_none());
        assert!(child.metadata.lean_signature_certificate.is_none());
    }
}
