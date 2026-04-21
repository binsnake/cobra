//! `SignatureSingletonPolyRecovery` pass — the "singleton + poly +
//! bitwise residual" lift. Three layers cooperate:
//!
//! 1. Per-variable univariate recovery via [`recover_singleton_powers`]
//!    captures each variable's squared / higher contribution.
//! 2. `CoB` coefficient splitting separates AND and MUL parts of the
//!    residual, guided by the singleton evaluations at `t=2`.
//! 3. The MUL side is lowered into a [`NormalizedPoly`] + AND residual;
//!    the AND residual is turned into an Expr by [`build_cob_expr`].
//!
//! For the current port, only the "zero residual" and
//! "`evaluator_override` inline" emission paths fire. The
//! non-zero-residual branch that emits a `RemainderStatePayload` for
//! Cluster 3's residual solvers is left out until those solvers
//! land — for now the pass returns `NoProgress` in that case so
//! other techniques can still try.

use cobra_core::evaluate_boolean_signature_from_evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::pass_contract::{ReasonDetail, VerificationState};
use cobra_core::result::Result;

use cobra_ir::{
    build_poly_expr, lower_arithmetic_fragment, normalize_polynomial, recover_singleton_powers,
    split_coefficients, UnivariateNormalizedPoly,
};
use cobra_orchestrator::{
    acquire_handle, submit_candidate, CandidateRecord, ItemDisposition, OrchestratorContext,
    PassDecision, PassId, PassResult, RemainderOrigin, RemainderStatePayload,
    RemainderTargetContext, StateData, WorkItem,
};

use crate::aux_var::eliminate_aux_vars;
use crate::cob_expr_builder::build_cob_expr;
use crate::decomposition_helpers::build_remainder_evaluator;
use crate::mapped_evaluator::build_mapped_evaluator;
use crate::singleton_power_expr_builder::build_singleton_power_expr;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

/// `S_i(2)` where `S_i` is the factorial-basis univariate for variable
/// `i`. Only degrees 1 and 2 contribute since the falling factorial
/// `(2)_k = 0` for `k >= 3`.
fn eval_univariate_at_2(poly: &UnivariateNormalizedPoly, bitwidth: u32) -> u64 {
    let mask = cobra_core::arith::bitmask(bitwidth);
    let mut sum = 0u64;
    for term in &poly.terms {
        if term.degree >= 3 {
            break;
        }
        sum = sum.wrapping_add(term.coeff.wrapping_mul(2)) & mask;
    }
    sum
}

fn bit_is_zero_constant(expr: &Expr) -> bool {
    matches!(expr.kind, cobra_core::expr::Kind::Constant(0))
}

/// Pass body. Produces a candidate that combines a singleton-power
/// expression, a polynomial lift, and a `CoB` residual.
#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_signature_singleton_poly_recovery(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::SignatureCoeff(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let sub = &payload.ctx;
    let coeffs = &payload.coeffs;
    let num_vars = sub.real_vars.len() as u32;

    // Match C++ `BuildMappedEvaluator`: use `evaluator_override` when
    // this pass runs inside a residual / lifted-outer signature solve,
    // otherwise fall back to the run-global evaluator, remapping
    // through `original_indices` when aux-var elimination has reduced
    // the variable space.
    let Some(eval) = build_mapped_evaluator(ctx, sub, item) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let singleton = recover_singleton_powers(&eval, num_vars, ctx.bitwidth).ok();

    let singleton_at_2: Vec<u64> = singleton
        .as_ref()
        .map(|sr| {
            (0..num_vars as usize)
                .map(|i| eval_univariate_at_2(&sr.per_var[i], ctx.bitwidth))
                .collect()
        })
        .unwrap_or_default();

    let split = split_coefficients(coeffs, &eval, num_vars, ctx.bitwidth, &singleton_at_2);
    let has_mul = split.mul_coeffs.iter().any(|&c| c != 0);

    let mut poly_expr: Option<Box<Expr>> = None;
    let mut residual = split.and_coeffs.clone();
    if has_mul {
        if let Ok(lowered) = lower_arithmetic_fragment(
            &split.and_coeffs,
            &split.mul_coeffs,
            num_vars as u8,
            ctx.bitwidth,
        ) {
            let normalized = normalize_polynomial(&lowered.poly);
            if let Ok(built) = build_poly_expr(&normalized) {
                poly_expr = Some(built);
                residual = lowered.residual_and_coeffs;
            }
        }
    }

    let singleton_expr = singleton.and_then(|s| build_singleton_power_expr(&s));
    let bit_expr = build_cob_expr(&residual, num_vars, ctx.bitwidth);
    let bit_is_zero = bit_is_zero_constant(&bit_expr);

    let mut prefix: Option<Box<Expr>> = poly_expr;
    if let Some(s) = singleton_expr {
        prefix = Some(match prefix {
            Some(p) => Expr::add(p, s),
            None => s,
        });
    }

    let group_id = item
        .group_id
        .expect("SignatureSingletonPolyRecovery requires a group_id");

    // Case A: zero residual — prefix alone is the full answer.
    if bit_is_zero {
        let candidate = prefix.unwrap_or_else(|| Expr::constant(0));
        let fw = full_width_check_eval(
            &eval,
            num_vars,
            &candidate,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !fw.passed {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: ReasonDetail::default(),
            });
        }
        let cost = compute_cost(&candidate).cost;
        submit_candidate(
            &mut ctx.competition_groups,
            group_id,
            CandidateRecord {
                expr: candidate,
                cost,
                verification: VerificationState::Verified,
                real_vars: sub.real_vars.clone(),
                source_pass: PassId::SignatureSingletonPolyRecovery,
                needs_original_space_verification: sub.needs_original_space_verification,
                sig_vector: sub.elimination.reduced_sig.clone(),
            },
        );
        return Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Case B: evaluator_override set — inline-combine to avoid the
    // residual → signature → residual cycle. Without `evaluator_override`
    // plumbed through this port, this branch can't fire yet, so we fall
    // through to "no progress". When Cluster 3 lands, switch this to
    // check `item.evaluator_override.is_some()`.
    if item.evaluator_override.is_some() {
        let mut combined: Option<Box<Expr>> = None;
        if !bit_is_zero {
            combined = Some(bit_expr);
        }
        if let Some(p) = prefix {
            combined = Some(match combined {
                Some(c) => Expr::add(c, p),
                None => p,
            });
        }
        let candidate = combined.unwrap_or_else(|| Expr::constant(0));
        let fw = full_width_check_eval(
            &eval,
            num_vars,
            &candidate,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !fw.passed {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: ReasonDetail::default(),
            });
        }
        let cost = compute_cost(&candidate).cost;
        submit_candidate(
            &mut ctx.competition_groups,
            group_id,
            CandidateRecord {
                expr: candidate,
                cost,
                verification: VerificationState::Verified,
                real_vars: sub.real_vars.clone(),
                source_pass: PassId::SignatureSingletonPolyRecovery,
                needs_original_space_verification: sub.needs_original_space_verification,
                sig_vector: sub.elimination.reduced_sig.clone(),
            },
        );
        return Ok(PassResult {
            decision: PassDecision::Advance,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    // Case C: non-zero residual at top level — emit a
    // `RemainderStatePayload` so the shared residual-solver table
    // (`ResidualSupported` / `ResidualPolyRecovery` / `ResidualTemplate`
    // for non-Boolean-null shapes, or the Ghost family for the
    // Boolean-null ones) can finish the job.

    // Guard: a 0-arity residual has nowhere to send its signature and
    // would make the downstream sample buffer zero-length. This
    // normally only happens when aux-var elimination reduced away all
    // inputs; let other techniques compete.
    if num_vars == 0 {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    acquire_handle(&mut ctx.competition_groups, group_id);

    let prefix_expr = prefix.unwrap_or_else(|| Expr::constant(0));
    let residual_eval = build_remainder_evaluator(&eval, &prefix_expr, ctx.bitwidth);
    let residual_sig =
        evaluate_boolean_signature_from_evaluator(&residual_eval, num_vars, ctx.bitwidth);
    let residual_elim = eliminate_aux_vars(&residual_sig, &sub.real_vars);
    let residual_support = build_var_support(&sub.real_vars, &residual_elim.real_vars);
    let is_bn = residual_sig.iter().all(|&s| s == 0);

    let payload = RemainderStatePayload {
        origin: RemainderOrigin::SignatureLowering,
        prefix_expr,
        prefix_degree: 0,
        remainder_eval: residual_eval,
        source_sig: sub.elimination.reduced_sig.clone(),
        remainder_sig: residual_sig,
        remainder_elim: residual_elim,
        remainder_support: residual_support,
        is_boolean_null: is_bn,
        degree_floor: 2,
        target: RemainderTargetContext {
            eval,
            vars: sub.real_vars.clone(),
            remap_support: Vec::new(),
        },
    };

    let mut residual_item = item.clone();
    residual_item.payload = StateData::Remainder(Box::new(payload));
    residual_item.attempted_mask = 0;
    residual_item.group_id = Some(group_id);

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![residual_item],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — signature-coeff-state items only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::SignatureCoeff(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::simplify_outcome::Options;
    use cobra_ir::interpolate_coefficients;
    use cobra_orchestrator::{
        create_group, EliminationResult, SignatureCoeffStatePayload, SignatureSubproblemContext,
    };

    fn mk_coeff_item(
        sig: Vec<u64>,
        real_vars: Vec<String>,
        ctx: &mut OrchestratorContext,
    ) -> WorkItem {
        let num_vars = real_vars.len() as u32;
        let coeffs = interpolate_coefficients(sig.clone(), num_vars, ctx.bitwidth);
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: real_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = SignatureCoeffStatePayload {
            ctx: SignatureSubproblemContext {
                sig,
                real_vars,
                elimination: elim,
                original_indices: Vec::new(),
                needs_original_space_verification: false,
            },
            coeffs,
        };
        let mut item = WorkItem::new(StateData::SignatureCoeff(Box::new(payload)));
        let gid = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        item.group_id = Some(gid);
        item
    }

    #[test]
    fn recovers_x_squared() {
        // f = x * x — at full width x² is not a bitwise expression; the
        // singleton power recovery catches it (univariate quadratic).
        let orig = Expr::mul(Expr::variable(0), Expr::variable(0));
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&orig, 64));

        // Signature at Boolean width of x² is [0, 1] — same as x.
        let item = mk_coeff_item(vec![0, 1], vec!["x".into()], &mut ctx);
        let gid = item.group_id.unwrap();

        let pr = run_signature_singleton_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);

        let best = ctx.competition_groups[&gid]
            .best
            .as_ref()
            .expect("candidate submitted");
        assert_eq!(best.source_pass, PassId::SignatureSingletonPolyRecovery);
        assert_eq!(best.verification, VerificationState::Verified);
    }

    #[test]
    fn linear_with_nonzero_constant_emits_remainder_state() {
        // f = x + 42 — the singleton lift captures x, leaving the
        // constant 42 in the AND residual. Case C emits a
        // `RemainderState` child so the shared residual-solver table
        // can close it out.
        let orig = Expr::add(Expr::variable(0), Expr::constant(42));
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&orig, 64));

        let item = mk_coeff_item(vec![42, 43], vec!["x".into()], &mut ctx);
        let pr = run_signature_singleton_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        assert!(matches!(pr.next[0].payload, StateData::Remainder(_)));
    }

    #[test]
    fn no_evaluator_returns_no_progress() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let item = mk_coeff_item(vec![0, 1], vec!["x".into()], &mut ctx);
        let pr = run_signature_singleton_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn non_coeff_payload_is_not_applicable() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::CompetitionResolved(
            cobra_orchestrator::CompetitionResolvedPayload { group_id: 0 },
        ));
        let pr = run_signature_singleton_poly_recovery(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
