//! `SemilinearNormalize` pass — lower a semantically-semilinear
//! `FoldedAst` item into a [`NormalizedSemilinearPayload`]. Gated on:
//!
//! - provenance != Lowered
//! - classification.semantic == Semilinear
//! - `is_linear_shortcut` returns false (linear inputs are handled by
//!   cheaper paths)
//! - `num_vars <= ctx.opts.max_vars`
//!
//! On normalisation failure returns `Blocked`; on gate failure returns
//! `NotApplicable` with `ConsumeCurrent` disposition so the item moves
//! on to other techniques.

use cobra_core::classification::SemanticClass;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame,
};
use cobra_core::result::Result;

use cobra_ir::{is_linear_shortcut, normalize_to_semilinear};
use cobra_orchestrator::{
    ItemDisposition, NormalizedSemilinearPayload, OrchestratorContext, PassDecision, PassResult,
    Provenance, SemilinearContext, StateData, WorkItem,
};

fn guard(msg: &'static str, category: ReasonCategory) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::Semilinear,
                subcode: 0,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

/// Pass body.
#[allow(clippy::unnecessary_wraps)]
pub fn run_semilinear_normalize(
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

    if matches!(item.features.provenance, Provenance::Lowered) {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let Some(cls) = ast.classification.as_ref() else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    if cls.semantic != SemanticClass::Semilinear {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Use the item's solve-ctx vars when a sub-problem is active
    // (lifting passes introduce virtual variables beyond
    // `ctx.original_vars` — hard-coding the global list would cause
    // the linear-shortcut probe to access out-of-range indices).
    let active_vars = match &ast.solve_ctx {
        Some(sc) => sc.vars.clone(),
        None => ctx.original_vars.clone(),
    };
    let num_vars = active_vars.len() as u32;

    if is_linear_shortcut(&ast.expr, num_vars, ctx.bitwidth) {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    if num_vars > ctx.opts.max_vars {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: guard(
                "too many variables for semilinear",
                ReasonCategory::GuardFailed,
            ),
        });
    }

    let Ok(ir) = normalize_to_semilinear(&ast.expr, &active_vars, ctx.bitwidth) else {
        let reason = guard(
            "semilinear normalization failed",
            ReasonCategory::RepresentationGap,
        );
        ctx.run_metadata.semilinear_failure = Some(reason.clone());
        return Ok(PassResult {
            decision: PassDecision::Blocked,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason,
        });
    };

    let evaluator = ctx.evaluator.clone();
    let payload = NormalizedSemilinearPayload {
        ctx: SemilinearContext {
            ir,
            vars: active_vars,
            evaluator,
        },
    };
    let mut next = item.clone();
    next.payload = StateData::SemilinearNormalized(Box::new(payload));

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![next],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — folded AST only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}
