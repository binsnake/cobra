//! `SignatureHybridDecompose` — fan-out pass that strips an
//! invertible operator (XOR or ADD) on a single variable, leaving a
//! residual sub-signature that recursively re-enters the signature
//! pipeline. Each candidate spawns a child solve guarded by a
//! `HybridComposeCont`. Recursion is gated to depth 0 (single level).

use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;

use cobra_orchestrator::{
    acquire_handle, create_group, ContinuationData, EliminationResult, HybridComposeCont,
    ItemDisposition, OrchestratorContext, PassDecision, PassResult, SignatureStatePayload,
    SignatureSubproblemContext, StateData, WorkItem,
};

use crate::hybrid_decomposer::enumerate_hybrid_candidates;

const MAX_CANDIDATES: usize = 8;

#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_signature_hybrid_decompose(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::Signature(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    if item.signature_recursion_depth >= 1 {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let sub_ctx = &payload.ctx;
    let sig = &sub_ctx.elimination.reduced_sig;
    let num_vars = sub_ctx.real_vars.len() as u32;
    if sig.len() < 2 || num_vars > 6 {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let parent_eval = ctx.evaluator.clone();
    if parent_eval.is_none() {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let mut candidates = enumerate_hybrid_candidates(sig, num_vars);
    if candidates.is_empty() {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }
    if candidates.len() > MAX_CANDIDATES {
        candidates.truncate(MAX_CANDIDATES);
    }

    let Some(parent_group_id) = item.group_id else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let mut next = Vec::new();
    for cand in candidates {
        acquire_handle(&mut ctx.competition_groups, parent_group_id);

        let child_group_id =
            create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        let cont = HybridComposeCont {
            var_k: cand.var_k,
            op: cand.op,
            parent_group_id,
            parent_eval: parent_eval.clone(),
            parent_real_vars: sub_ctx.real_vars.clone(),
            parent_original_indices: sub_ctx.original_indices.clone(),
            parent_num_vars: num_vars,
            parent_needs_original_space_verification: sub_ctx.needs_original_space_verification,
        };
        ctx.competition_groups
            .get_mut(&child_group_id)
            .expect("group just created")
            .continuation = Some(ContinuationData::HybridCompose(Box::new(cont)));

        let child_elim = EliminationResult {
            reduced_sig: cand.r_sig.clone(),
            real_vars: sub_ctx.real_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let mut child = WorkItem::new(StateData::Signature(Box::new(SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig: cand.r_sig,
                real_vars: sub_ctx.real_vars.clone(),
                elimination: child_elim,
                original_indices: sub_ctx.original_indices.clone(),
                needs_original_space_verification: false,
            },
        })));
        child.features = item.features.clone();
        child.metadata = item.metadata.clone();
        child.depth = item.depth;
        child.rewrite_gen = item.rewrite_gen;
        child.attempted_mask = 0;
        child.signature_recursion_depth = item.signature_recursion_depth + 1;
        child.group_id = Some(child_group_id);
        child
            .evaluator_override
            .clone_from(&item.evaluator_override);
        child.evaluator_override_arity = item.evaluator_override_arity;
        child.history.clone_from(&item.history);

        next.push(child);
    }

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next,
        reason: ReasonDetail::default(),
    })
}

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Signature(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{create_group as orch_create_group, EliminationResult};

    fn mk_sig_item(sig: &[u64], vars: Vec<String>, ctx: &mut OrchestratorContext) -> WorkItem {
        let sig = sig.to_vec();
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig: sig.clone(),
                real_vars: vars,
                elimination: elim,
                original_indices: (0..sig.len() as u32).collect(),
                needs_original_space_verification: false,
            },
        };
        let mut item = WorkItem::new(StateData::Signature(Box::new(payload)));
        let gid = orch_create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        item.group_id = Some(gid);
        item
    }

    #[test]
    fn fans_out_one_child_per_candidate() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let f = Expr::xor(Expr::variable(0), Expr::variable(1));
        ctx.evaluator = Some(Evaluator::from_expr(&f, 64));
        let item = mk_sig_item(&[0u64, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        let pr = run_signature_hybrid_decompose(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        for child in &pr.next {
            let gid = child.group_id.unwrap();
            assert!(matches!(
                ctx.competition_groups[&gid].continuation,
                Some(ContinuationData::HybridCompose(_))
            ));
        }
    }

    #[test]
    fn recursion_depth_guard_blocks_at_depth_one() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(
            &Expr::xor(Expr::variable(0), Expr::variable(1)),
            64,
        ));
        let mut item = mk_sig_item(&[0u64, 1, 1, 0], vec!["x".into(), "y".into()], &mut ctx);
        item.signature_recursion_depth = 1;
        let pr = run_signature_hybrid_decompose(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }
}
