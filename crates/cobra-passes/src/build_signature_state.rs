//! `RunBuildSignatureState` pass — the bridge from `FoldedAst` to
//! fast-path helpers (`TryConstantSignatureCandidate`,
//! `TryBooleanAnfFastPath`) deferred until their dependencies
//! (pattern matcher, ANF transform, product-shadow repair + spot-check
//! wiring) are ported.

use cobra_core::evaluate_boolean_signature;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr_rewrite::build_var_support;
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::{err, CobraError, Result};

use cobra_orchestrator::{
    acquire_handle, create_group, ItemDisposition, OrchestratorContext, PassDecision, PassResult,
    SignatureStatePayload, SignatureSubproblemContext, StateData, WorkItem,
};

use crate::aux_var::{eliminate_aux_vars, eliminate_aux_vars_fw};

/// (without the two optional fast paths).
pub fn run_build_signature_state(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::ConsumeCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let (active_vars, active_eval_is_some) = active_vars_and_eval_flag(item, ctx);
    let num_vars = active_vars.len() as u32;

    // Step 1: signature.
    // Reuse `ctx.input_sig` / `solve_ctx.input_sig` when available and
    // still fresh (no lowering, no rewrites). Otherwise recompute from
    // the AST.
    let use_input_sig =
        active_input_sig(item, ctx).is_some() && !ctx.lowering_fired && item.rewrite_gen == 0;
    let sig = if use_input_sig {
        active_input_sig(item, ctx).expect("guarded above").clone()
    } else {
        evaluate_boolean_signature(&ast.expr, num_vars, ctx.bitwidth)
    };

    // Step 2: aux-var elimination. When an active evaluator is
    // available, use the full-width overload so variables spurious on
    // `{0, 1}` but live at full bitwidth (e.g. `x*y` vs `x&y`) stay
    // in `real_vars`.
    let active_eval = active_eval(item, ctx);
    let elim = if let Some(eval) = active_eval.as_ref() {
        eliminate_aux_vars_fw(&sig, &active_vars, eval, ctx.bitwidth)
    } else {
        eliminate_aux_vars(&sig, &active_vars)
    };
    let real_var_count = elim.real_vars.len() as u32;
    if real_var_count > ctx.opts.max_vars {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "Variable count after elimination ({}) exceeds max_vars ({})",
                real_var_count, ctx.opts.max_vars
            ),
        ));
    }

    // Step 3: var-support remap.
    let original_indices = build_var_support(&active_vars, &elim.real_vars);

    // Step 4: verification guard — if the active evaluator is present,
    // the eventual candidate will need full-width verification.
    let needs_verification = active_eval_is_some;

    // Step 5: seed the signature-state item.
    let seed = SignatureStatePayload {
        ctx: SignatureSubproblemContext {
            sig,
            real_vars: elim.real_vars.clone(),
            elimination: elim,
            original_indices,
            needs_original_space_verification: needs_verification,
        },
    };

    let mut sig_seed = item.clone();
    sig_seed.payload = StateData::Signature(Box::new(seed));
    sig_seed.metadata.lean_certificate = None;
    sig_seed.metadata.lean_signature_certificate = None;
    sig_seed.evaluator_override = active_eval;
    sig_seed.evaluator_override_arity = num_vars;
    let group_id = if let Some(gid) = item.group_id {
        acquire_handle(&mut ctx.competition_groups, gid);
        gid
    } else {
        create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None)
    };
    sig_seed.group_id = Some(group_id);
    // `SignatureState` items are band-1 in the scheduler; no need to
    // tweak features here.

    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::RetainCurrent,
        next: vec![sig_seed],
        reason: ReasonDetail::default(),
    })
}

/// Applicability guard — `FoldedAst` only.
#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}

// ---------------------------------------------------------------
// Active-view helpers (replicating C++ `ActiveAstVars`,
// `ActiveAstEvaluator`, `ActiveAstInputSig`)
// ---------------------------------------------------------------

/// Returns the solve-ctx vars when present, otherwise `ctx.original_vars`.
/// Second element: true iff an active evaluator is available.
fn active_vars_and_eval_flag(item: &WorkItem, ctx: &OrchestratorContext) -> (Vec<String>, bool) {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = ast.solve_ctx.as_ref() {
            let has_eval = sc.evaluator.is_some();
            return (sc.vars.clone(), has_eval);
        }
    }
    let has_eval = ctx.evaluator.is_some();
    (ctx.original_vars.clone(), has_eval)
}

/// Returns the active evaluator — solve-ctx-local if present,
/// otherwise `ctx.evaluator`.
fn active_eval(item: &WorkItem, ctx: &OrchestratorContext) -> Option<Evaluator> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = ast.solve_ctx.as_ref() {
            if sc.evaluator.is_some() {
                return sc.evaluator.clone();
            }
        }
    }
    ctx.evaluator.clone()
}

/// available and non-empty. Prefers the item-local solve context, then
/// falls back to `ctx.input_sig`.
fn active_input_sig<'a>(item: &'a WorkItem, ctx: &'a OrchestratorContext) -> Option<&'a Vec<u64>> {
    if let StateData::FoldedAst(ast) = &item.payload {
        if let Some(sc) = ast.solve_ctx.as_ref() {
            if !sc.input_sig.is_empty() {
                return Some(&sc.input_sig);
            }
        }
    }
    if ctx.input_sig.is_empty() {
        None
    } else {
        Some(&ctx.input_sig)
    }
}

// Silence unused-`Evaluator` import warning — the active-eval flag
// checks only `is_some()`, but keeping the type imported makes the
// signature documentation above self-referential.
#[allow(dead_code)]
fn _reference_evaluator_type(_e: &Evaluator) {}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;
    use cobra_orchestrator::{create_group as orch_create_group, AstPayload, Provenance};

    fn mk_ast_item(expr: Box<Expr>, prov: Provenance) -> WorkItem {
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: prov,
            solve_ctx: None,
        })));
        item.features.provenance = prov;
        item
    }

    #[test]
    fn build_signature_state_emits_signature_payload() {
        // "x + y" at bitwidth 64, 2 vars.
        let expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut item = mk_ast_item(expr, Provenance::Lowered);
        item.metadata.lean_certificate = Some(cobra_orchestrator::LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::variable(0),
        ));
        item.metadata.lean_signature_certificate =
            cobra_orchestrator::LeanSignatureCertificate::new(64, 1, vec![0, 1], Expr::variable(0));
        let pr = run_build_signature_state(&item, &mut ctx).unwrap();
        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        match &pr.next[0].payload {
            StateData::Signature(sig) => {
                assert_eq!(sig.ctx.real_vars, vec!["x".to_owned(), "y".to_owned()]);
                assert_eq!(sig.ctx.sig.len(), 4);
                assert_eq!(sig.ctx.original_indices, vec![0, 1]);
                assert!(!sig.ctx.needs_original_space_verification);
            }
            _ => panic!("expected Signature payload"),
        }
        assert_eq!(pr.next[0].group_id, Some(0));
        assert!(pr.next[0].metadata.lean_certificate.is_none());
        assert!(pr.next[0].metadata.lean_signature_certificate.is_none());
        assert!(pr.next[0].evaluator_override.is_none());
        assert_eq!(pr.next[0].evaluator_override_arity, 2);
        assert_eq!(ctx.next_group_id, 1);
        assert_eq!(ctx.competition_groups[&0].open_handles, 1);
    }

    #[test]
    fn build_signature_state_preserves_solve_ctx_evaluator_override() {
        let outer = Expr::and(Expr::variable(2), Expr::variable(0));
        let solve_ctx = cobra_orchestrator::AstSolveContext {
            vars: vec!["x".into(), "y".into(), "v0".into()],
            evaluator: Some(Evaluator::from_expr(&outer, 64)),
            input_sig: vec![],
        };
        let mut item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr: outer,
            classification: None,
            provenance: Provenance::Rewritten,
            solve_ctx: Some(solve_ctx),
        })));
        item.features.provenance = Provenance::Rewritten;
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);

        let pr = run_build_signature_state(&item, &mut ctx).unwrap();

        assert_eq!(pr.decision, PassDecision::Advance);
        assert!(pr.next[0].evaluator_override.is_some());
        assert_eq!(pr.next[0].evaluator_override_arity, 3);
    }

    #[test]
    fn build_signature_state_eliminates_spurious_vars() {
        // "x" in a 2-variable context — `y` is spurious.
        let expr = Expr::variable(0);
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let item = mk_ast_item(expr, Provenance::Lowered);
        let pr = run_build_signature_state(&item, &mut ctx).unwrap();
        match &pr.next[0].payload {
            StateData::Signature(sig) => {
                assert_eq!(sig.ctx.real_vars, vec!["x".to_owned()]);
                assert_eq!(sig.ctx.elimination.spurious_vars, vec!["y".to_owned()]);
                assert_eq!(sig.ctx.sig.len(), 4); // original sig kept; real_vars drives reduced form.
                assert_eq!(sig.ctx.original_indices, vec![0]);
            }
            _ => panic!("expected Signature payload"),
        }
    }

    #[test]
    fn build_signature_state_errors_on_too_many_vars() {
        // Three real vars, max_vars clamped to 2 → ToManyVariables error.
        let expr = Expr::add(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let opts = Options {
            max_vars: 2,
            ..Options::default()
        };
        let mut ctx = OrchestratorContext::new(opts, vec!["x".into(), "y".into(), "z".into()], 64);
        let item = mk_ast_item(expr, Provenance::Lowered);
        let e = run_build_signature_state(&item, &mut ctx).unwrap_err();
        assert_eq!(e.code, CobraError::TooManyVariables);
    }

    #[test]
    fn build_signature_state_reuses_incoming_group() {
        let expr = Expr::variable(0);
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 64);
        let gid = orch_create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
        let mut item = mk_ast_item(expr, Provenance::Lowered);
        item.group_id = Some(gid);

        let pr = run_build_signature_state(&item, &mut ctx).unwrap();

        assert_eq!(pr.decision, PassDecision::Advance);
        assert_eq!(pr.next.len(), 1);
        assert_eq!(pr.next[0].group_id, Some(gid));
        assert_eq!(ctx.next_group_id, 1);
        assert_eq!(ctx.competition_groups[&gid].open_handles, 2);
    }
}
