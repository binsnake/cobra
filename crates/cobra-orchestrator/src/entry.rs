//! Top-level convenience entry points over [`crate::main_loop`]. A full
//! public `simplify(sig, vars, input_expr, opts)` that performs its own
//! seeding lands once the classifier and pattern-match passes are
//! ported; until then, `simplify_from_worklist` lets tests and early
//! integration exercise the dispatch end-to-end.

use cobra_core::expr::Expr;
use cobra_core::expr_rewrite::cleanup_final_expr;
use cobra_core::pass_contract::{PassOutcome, VerificationState};
use cobra_core::result::Result;
use cobra_core::simplify_outcome::{
    Diagnostic, SimplifyOutcome, SimplifyOutcomeKind, SimplifyTelemetry,
};

use crate::context::{OrchestratorContext, OrchestratorPolicy};
use crate::main_loop::{run_main_loop, LoopResult};
use crate::registry::PassDescriptor;
use crate::worklist::Worklist;

/// Run the main loop against a pre-seeded worklist and convert the
/// result to a public [`SimplifyOutcome`].
///
/// `original_expr`, when supplied, is cloned into the outcome's `expr`
/// field on the "unsupported" path so the caller sees the input
/// expression echoed back. When `None`, the unsupported path leaves
/// `expr` as `None`.
pub fn simplify_from_worklist(
    ctx: &mut OrchestratorContext,
    mut worklist: Worklist,
    mut policy: OrchestratorPolicy,
    registry: &[PassDescriptor],
    original_expr: Option<&Expr>,
) -> Result<SimplifyOutcome> {
    let result = run_main_loop(ctx, &mut worklist, &mut policy, registry, original_expr)?;
    Ok(to_simplify_outcome(result, original_expr, ctx.bitwidth))
}

/// Convert a [`LoopResult`] to a public [`SimplifyOutcome`]. Matches C++
/// `ToSimplifyOutcome`: success runs `cleanup_final_expr` on the expr,
/// failure either echoes the input or leaves `expr = None`.
pub fn to_simplify_outcome(
    result: LoopResult,
    original_expr: Option<&Expr>,
    bitwidth: u32,
) -> SimplifyOutcome {
    let mut outcome = SimplifyOutcome::default();

    match result.outcome {
        PassOutcome::Success {
            expr,
            real_vars,
            verification,
            ..
        } => {
            outcome.kind = SimplifyOutcomeKind::Simplified;
            outcome.expr = Some(cleanup_final_expr(expr, bitwidth));
            outcome.real_vars = real_vars;
            outcome.verified = verification == VerificationState::Verified;
            outcome.sig_vector = result.metadata.sig_vector;
        }
        other => {
            outcome.kind = SimplifyOutcomeKind::UnchangedUnsupported;
            outcome.expr = original_expr.map(|e| Box::new(e.clone()));
            // Pull the reason's top-level message into the diagnostic.
            if let PassOutcome::Blocked(reason) | PassOutcome::Inapplicable(reason) = &other {
                outcome.diag.reason.clone_from(&reason.top.message);
            }
        }
    }

    let existing_reason = std::mem::take(&mut outcome.diag.reason);
    outcome.diag = Diagnostic {
        classification: result.run_metadata.input_classification,
        structural_transform_rounds: result.metadata.structural_transform_rounds,
        transform_produced_candidate: result.metadata.transform_produced_candidate,
        candidate_failed_verification: result.metadata.candidate_failed_verification,
        reason: existing_reason,
        reason_code: result.metadata.reason_code,
        cause_chain: result.metadata.cause_chain,
    };

    outcome.telemetry = SimplifyTelemetry {
        total_expansions: result.telemetry.total_expansions,
        max_depth_reached: result.telemetry.max_depth_reached,
        candidates_verified: result.telemetry.candidates_verified,
        queue_high_water: result.telemetry.queue_high_water,
    };

    outcome
}
