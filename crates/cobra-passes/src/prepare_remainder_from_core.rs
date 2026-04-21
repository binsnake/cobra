//! `PrepareRemainderFromCore` pass — given a `CoreCandidatePayload`,
//! build `r(x) = f(x) - core(x)` as a remainder evaluator, sample its
//! Boolean signature, run aux-var elimination, and emit a
//! `RemainderStatePayload` tagged by the core's extractor origin.
//!
//! The `degree_floor` is `degree_used + 1` for polynomial cores (the
//! next residual-poly attempt must escalate) and `2` otherwise.

use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, VerificationState,
};
use cobra_core::result::Result;

use cobra_orchestrator::{
    CandidatePayload, ExtractorKind, ItemDisposition, OrchestratorContext, PassDecision, PassId,
    PassResult, RemainderOrigin, RemainderStatePayload, RemainderTargetContext, StateData,
    WorkItem,
};

use crate::aux_var::eliminate_aux_vars;
use crate::decomposition_helpers::build_remainder_evaluator;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn origin_for(kind: ExtractorKind) -> RemainderOrigin {
    match kind {
        ExtractorKind::ProductAst => RemainderOrigin::ProductCore,
        ExtractorKind::Polynomial => RemainderOrigin::PolynomialCore,
        ExtractorKind::Template => RemainderOrigin::TemplateCore,
        ExtractorKind::BooleanNullDirect => RemainderOrigin::DirectBooleanNull,
    }
}

fn is_boolean_null_sig(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v == 0)
}

fn reason(msg: &'static str, subcode: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::GuardFailed,
                domain: ReasonDomain::Decomposition,
                subcode,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

/// Pass body.
#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_prepare_remainder_from_core(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::CoreCandidate(core) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    if core.target.vars.is_empty() && ctx.evaluator.is_none() {
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: reason("Decomposition requires evaluator", 11),
        });
    }

    let target_vars: Vec<String> = if core.target.vars.is_empty() {
        ctx.original_vars.clone()
    } else {
        core.target.vars.clone()
    };
    let target_eval = if core.target.vars.is_empty() {
        ctx.evaluator.clone().expect("guarded above")
    } else {
        core.target.eval.clone()
    };
    let num_vars = target_vars.len() as u32;

    let residual_eval = build_remainder_evaluator(&target_eval, &core.core_expr, ctx.bitwidth);
    // Evaluate residual on Boolean assignments — direct evaluation of
    // the closure at every 0/1 point.
    let mut residual_sig = vec![0u64; 1usize << num_vars];
    let mut point = vec![0u64; num_vars as usize];
    for (i, slot) in residual_sig.iter_mut().enumerate() {
        for (k, p) in point.iter_mut().enumerate() {
            *p = ((i >> k) & 1) as u64;
        }
        *slot = residual_eval.eval(&point);
    }

    // Constant-residual short-circuit: when every Boolean-point
    // residual evaluates to the same value, the residual is literally
    // a constant at full width (barring carry effects — verified
    // below). Emit `prefix + constant` as a candidate directly so
    // the residual-solver chain doesn't have to recover a zero-arity
    // polynomial. Fixes e.g. `(x&y)*(x|y) + (x&~y)*(~x&y) − 41 →
    // x*y − 41`, where `ExtractProductCore` strips out `x*y` and
    // leaves `−41` as the residual.
    let all_equal = residual_sig.windows(2).all(|w| w[0] == w[1]);
    if all_equal {
        let constant = residual_sig[0];
        let candidate = if constant == 0 {
            core.core_expr.clone_tree()
        } else {
            Expr::add(core.core_expr.clone_tree(), Expr::constant(constant))
        };
        let chk = full_width_check_eval(
            &target_eval,
            num_vars,
            &candidate,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if chk.passed {
            let cost = compute_cost(&candidate).cost;
            let payload = CandidatePayload {
                expr: candidate,
                real_vars: target_vars.clone(),
                cost,
                producing_pass: PassId::PrepareRemainderFromCore,
                needs_original_space_verification: false,
            };
            let mut next = item.clone();
            next.payload = StateData::Candidate(Box::new(payload));
            next.metadata.verification = VerificationState::Verified;
            return Ok(PassResult {
                decision: PassDecision::SolvedCandidate,
                disposition: ItemDisposition::ConsumeCurrent,
                next: vec![next],
                reason: ReasonDetail::default(),
            });
        }
    }

    let elim = eliminate_aux_vars(&residual_sig, &target_vars);
    let support = build_var_support(&target_vars, &elim.real_vars);
    let is_bn = is_boolean_null_sig(&residual_sig);

    let degree_floor = if matches!(core.extractor_kind, ExtractorKind::Polynomial) {
        core.degree_used.saturating_add(1)
    } else {
        2
    };

    let payload = RemainderStatePayload {
        origin: origin_for(core.extractor_kind),
        prefix_expr: core.core_expr.clone_tree(),
        prefix_degree: core.degree_used,
        remainder_eval: residual_eval,
        source_sig: core.source_sig.clone(),
        remainder_sig: residual_sig,
        remainder_elim: elim,
        remainder_support: support,
        is_boolean_null: is_bn,
        degree_floor,
        target: RemainderTargetContext {
            eval: target_eval,
            vars: target_vars,
            remap_support: core.target.remap_support.clone(),
        },
    };

    let mut next = item.clone();
    next.payload = StateData::Remainder(Box::new(payload));

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![next],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — core candidate only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::CoreCandidate(_))
}
