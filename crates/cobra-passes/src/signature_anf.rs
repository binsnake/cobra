//! `SignatureAnf` pass — converts a Boolean-valued signature into its
//! algebraic normal form, then cost-optimises the resulting XOR/AND
//! tree via [`cobra_ir::cleanup_anf`]. Emits a verified
//! `CandidatePayload` on success.
//!
//! A spot-check against the signature vector runs before the
//! full-width check. When an evaluator is available the full-width
//! check is authoritative — and if it fails on the raw ANF tree, the
//! pass retries with `repair_product_shadow` to account for the
//! `AND == MUL` equivalence on `{0, 1}` not holding at full width.

use cobra_core::expr::Expr;
use cobra_core::expr_cost::compute_cost;
use cobra_core::expr_rewrite::repair_product_shadow;
use cobra_core::pass_contract::{ReasonDetail, VerificationState};
use cobra_core::result::Result;

use cobra_ir::{build_anf_expr, compute_anf};
use cobra_orchestrator::{
    submit_candidate, CandidatePayload, CandidateRecord, ItemDisposition, OrchestratorContext,
    PassDecision, PassId, PassResult, StateData, WorkItem,
};

use crate::mapped_evaluator::build_mapped_evaluator;
use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

fn is_boolean_sig(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v <= 1)
}

/// Pass body. Returns `NotApplicable` for non-signature payloads,
/// `NoProgress` when the signature isn't Boolean or exceeds
/// `opts.max_vars`, or when no verifier accepts the emitted tree.
#[allow(clippy::unnecessary_wraps, clippy::too_many_lines)]
pub fn run_signature_anf(item: &WorkItem, ctx: &mut OrchestratorContext) -> Result<PassResult> {
    let StateData::Signature(payload) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };
    let sub = &payload.ctx;
    let sig = &sub.elimination.reduced_sig;
    let num_vars = sub.real_vars.len() as u32;

    if !is_boolean_sig(sig) || num_vars > ctx.opts.max_vars {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    }

    let packed = compute_anf(sig, num_vars);
    let mut anf_expr: Box<Expr> = build_anf_expr(&packed, num_vars);

    // Spot check against the signature vector — cheap, rejects any
    // ANF-builder bug before a candidate enters the verification budget.
    if ctx.opts.spot_check {
        let emitted = cobra_core::evaluate_boolean_signature(&anf_expr, num_vars, ctx.bitwidth);
        let matches = sig
            .iter()
            .zip(emitted.iter())
            .all(|(&a, &b)| (a & 1) == (b & 1));
        if !matches {
            return Ok(PassResult {
                decision: PassDecision::NoProgress,
                disposition: ItemDisposition::RetainCurrent,
                next: Vec::new(),
                reason: ReasonDetail::default(),
            });
        }
    }

    // Full-width check against the mapped evaluator when available.
    // Retry with `repair_product_shadow` before giving up — ANF is
    // built over GF(2) so `AND` and `MUL` collapse on {0,1}; at full
    // width the two differ.
    if let Some(mapped) = build_mapped_evaluator(ctx, sub, item) {
        let check = full_width_check_eval(
            &mapped,
            num_vars,
            &anf_expr,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !check.passed {
            let repaired = repair_product_shadow(anf_expr.clone_tree());
            let repair_check = full_width_check_eval(
                &mapped,
                num_vars,
                &repaired,
                ctx.bitwidth,
                DEFAULT_NUM_SAMPLES,
            );
            if !repair_check.passed {
                return Ok(PassResult {
                    decision: PassDecision::NoProgress,
                    disposition: ItemDisposition::RetainCurrent,
                    next: Vec::new(),
                    reason: ReasonDetail::default(),
                });
            }
            anf_expr = repaired;
        }
    }

    // Like `signature_pattern_match`: candidates owned by a
    // competition group (residual / lifted-outer sub-problems) must
    // go through the group's continuation (e.g. `RemainderRecombine`)
    // rather than through `VerifyCandidate` against the top-level
    // evaluator.
    let cost = compute_cost(&anf_expr).cost;
    if let Some(gid) = item.group_id {
        submit_candidate(
            &mut ctx.competition_groups,
            gid,
            CandidateRecord {
                expr: anf_expr,
                cost,
                verification: VerificationState::Verified,
                real_vars: sub.real_vars.clone(),
                source_pass: PassId::SignatureAnf,
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

    let candidate = CandidatePayload {
        expr: anf_expr,
        real_vars: sub.real_vars.clone(),
        cost,
        producing_pass: PassId::SignatureAnf,
        needs_original_space_verification: sub.needs_original_space_verification,
    };
    let mut child = item.clone();
    child.payload = StateData::Candidate(Box::new(candidate));
    child.metadata.verification = VerificationState::Verified;
    child.metadata.sig_vector.clone_from(sig);

    Ok(PassResult {
        decision: PassDecision::SolvedCandidate,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![child],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — signature-state items only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::Signature(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Kind;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{
        EliminationResult, SignatureStatePayload, SignatureSubproblemContext,
    };

    fn mk_sig_item(sig: Vec<u64>, real_vars: Vec<String>, needs_verify: bool) -> WorkItem {
        let elim = EliminationResult {
            reduced_sig: sig.clone(),
            real_vars: real_vars.clone(),
            spurious_vars: Vec::new(),
        };
        let payload = SignatureStatePayload {
            ctx: SignatureSubproblemContext {
                sig,
                real_vars,
                elimination: elim,
                original_indices: Vec::new(),
                needs_original_space_verification: needs_verify,
            },
        };
        WorkItem::new(StateData::Signature(Box::new(payload)))
    }

    #[test]
    fn anf_recovers_three_var_xor() {
        // f = x ^ y ^ z (3 vars) — a case the 2-var pattern table
        // cannot handle but ANF recovers exactly.
        let sig = vec![0, 1, 1, 0, 1, 0, 0, 1];
        let mut ctx = OrchestratorContext::new(
            Options::default(),
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let expr = Expr::xor(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
        let item = mk_sig_item(sig, vec!["x".into(), "y".into(), "z".into()], false);

        let pr = run_signature_anf(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        assert_eq!(pr.next.len(), 1);
        let StateData::Candidate(c) = &pr.next[0].payload else {
            panic!("expected Candidate payload");
        };
        // Signature must still match after recovery.
        let recovered = cobra_core::evaluate_boolean_signature(&c.expr, 3, 64);
        assert_eq!(recovered, vec![0, 1, 1, 0, 1, 0, 0, 1]);
    }

    #[test]
    fn anf_non_boolean_sig_returns_no_progress() {
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        // sig = [0, 1, 1, 2] — three distinct values, not Boolean.
        let item = mk_sig_item(vec![0, 1, 1, 2], vec!["x".into(), "y".into()], false);
        let pr = run_signature_anf(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn anf_exceeds_max_vars_returns_no_progress() {
        let mut ctx = OrchestratorContext::new(
            Options {
                max_vars: 2,
                ..Options::default()
            },
            vec!["x".into(), "y".into(), "z".into()],
            64,
        );
        let sig = vec![0u64; 8];
        let item = mk_sig_item(sig, vec!["x".into(), "y".into(), "z".into()], false);
        let pr = run_signature_anf(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NoProgress);
    }

    #[test]
    fn anf_product_shadow_repair_recovers_mul_over_boolean_sig() {
        // f(x, y) = x * y — at Boolean width the signature is
        // identical to x & y, so the ANF builder emits `x & y`. The
        // full-width check against the original `x * y` evaluator
        // fails; `repair_product_shadow` then substitutes MUL for
        // AND and the retry passes.
        let original = Expr::mul(Expr::variable(0), Expr::variable(1));
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        ctx.evaluator = Some(Evaluator::from_expr(&original, 64));
        let item = mk_sig_item(vec![0, 0, 0, 1], vec!["x".into(), "y".into()], false);

        let pr = run_signature_anf(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::SolvedCandidate);
        let StateData::Candidate(c) = &pr.next[0].payload else {
            panic!("expected Candidate payload");
        };
        // After repair the top op must be Mul, not And.
        assert!(matches!(c.expr.kind, Kind::Mul));
    }

    #[test]
    fn anf_noop_on_non_signature_payload() {
        let mut ctx = OrchestratorContext::new(Options::default(), vec![], 64);
        let item = WorkItem::new(StateData::Candidate(Box::new(CandidatePayload {
            expr: Expr::variable(0),
            real_vars: Vec::new(),
            cost: cobra_core::expr_cost::ExprCost::default(),
            producing_pass: PassId::VerifyCandidate,
            needs_original_space_verification: false,
        })));
        let pr = run_signature_anf(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::NotApplicable);
    }
}
