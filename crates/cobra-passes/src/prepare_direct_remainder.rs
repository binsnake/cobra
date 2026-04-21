//! `PrepareDirectRemainder` pass — detect when the current AST's
//! signature already evaluates to `{0, 1}` at full width, and
//! construct a `RemainderStatePayload` tagged as a direct Boolean-null
//! residual. Downstream residual solvers handle the actual work.
//!
//! Gated on an available evaluator — without one, there's no way to
//! probe full-width equality.

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    ItemDisposition, OrchestratorContext, PassDecision, PassResult, RemainderOrigin,
    RemainderStatePayload, RemainderTargetContext, StateData, WorkItem,
};

use crate::aux_var::eliminate_aux_vars;

fn reason(msg: &'static str, category: ReasonCategory, subcode: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::Decomposition,
                subcode,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn is_boolean_null_sig(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v == 0)
}

/// Pass body.
#[allow(clippy::unnecessary_wraps)]
pub fn run_prepare_direct_remainder(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let Some(eval) = ctx.evaluator.clone() else {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: reason(
                "Decomposition requires evaluator",
                ReasonCategory::GuardFailed,
                10,
            ),
        });
    };

    let active_vars = ctx.original_vars.clone();
    let num_vars = active_vars.len() as u32;

    // Compute the decomposition signature as the Boolean-width
    // evaluation of the AST. This is the residual candidate.
    let decomp_sig = evaluate_boolean_signature(&ast.expr, num_vars, ctx.bitwidth);

    let elim = eliminate_aux_vars(&decomp_sig, &active_vars);
    let support = build_var_support(&active_vars, &elim.real_vars);

    if !is_boolean_null_sig(&decomp_sig) {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let payload = RemainderStatePayload {
        origin: RemainderOrigin::DirectBooleanNull,
        prefix_expr: cobra_core::expr::Expr::constant(0),
        prefix_degree: 0,
        remainder_eval: eval.clone(),
        source_sig: decomp_sig.clone(),
        remainder_sig: decomp_sig,
        remainder_elim: elim,
        remainder_support: support,
        is_boolean_null: true,
        degree_floor: 2,
        target: RemainderTargetContext {
            eval,
            vars: active_vars,
            remap_support: Vec::new(),
        },
    };

    let mut next = item.clone();
    next.payload = StateData::Remainder(Box::new(payload));

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![next],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — folded AST only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}
