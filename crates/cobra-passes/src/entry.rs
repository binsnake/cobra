//! Public simplifier entry points that own seeding plus orchestrator dispatch.
//!
//! This is the Rust equivalent of upstream `Simplify`: validate public inputs,
//! seed either from an AST or from a Boolean signature, then run the pass
//! registry to a [`cobra_core::simplify_outcome::SimplifyOutcome`].

use cobra_core::arith::bitmask;
use cobra_core::evaluator::{Evaluator, TraceKind};
use cobra_core::expr::{Expr, Kind};
use cobra_core::pass_contract::VerificationState;
use cobra_core::result::{err, CobraError, Result};
use cobra_core::simplify_outcome::{Options, SimplifyOutcome, SimplifyOutcomeKind};
use cobra_core::{evaluate_boolean_signature, is_valid_bitwidth};
use cobra_ir::{contains_shr, detect_root_low_bit_mask};

use cobra_orchestrator::{
    create_group, simplify_from_worklist, OrchestratorContext, OrchestratorPolicy, Provenance,
    SignatureStatePayload, SignatureSubproblemContext, StateData, WorkItem, Worklist,
};

use crate::aux_var::eliminate_aux_vars;
use crate::pattern_matcher::match_pattern;
use crate::seed::seed_with_ast;
use crate::spot_check::{full_width_check_eval, verify_in_original_space, DEFAULT_NUM_SAMPLES};
use crate::PASS_REGISTRY;

/// Upper bound checked before any `2^vars.len()` signature allocation.
pub const MAX_INPUT_VARS: usize = 24;

/// Run the complete simplifier pipeline from a Boolean signature and,
/// optionally, an original AST.
///
/// When `input_expr` is present, the function can build an evaluator from it
/// unless `opts.evaluator` already supplies one. When `input_expr` is `None`,
/// the signature-only path is used and full-width verification is available
/// only if `opts.evaluator` was supplied.
pub fn simplify(
    sig: &[u64],
    vars: &[String],
    input_expr: Option<&Expr>,
    opts: Options,
) -> Result<SimplifyOutcome> {
    validate_public_inputs(sig, vars, opts.bitwidth)?;

    if let Some(expr) = input_expr {
        if let Some(result) = try_dynamic_mask(sig, vars, expr, &opts)? {
            return Ok(result);
        }
    }

    let mut ctx = build_context(sig, vars, input_expr, opts);
    if input_expr.is_none() {
        if let Some(result) = try_no_ast_constant_seed(sig, vars, &ctx) {
            return Ok(result);
        }
    }

    let mut worklist = Worklist::new();
    match input_expr {
        Some(expr) => seed_with_ast(expr, &mut ctx, &mut worklist)?,
        None => seed_no_ast(sig, vars, &mut ctx, &mut worklist)?,
    }

    simplify_from_worklist(
        &mut ctx,
        worklist,
        OrchestratorPolicy::default(),
        PASS_REGISTRY,
        input_expr,
    )
}

/// Convenience wrapper for callers that have an AST and want the Boolean
/// signature computed from it.
pub fn simplify_expr(expr: &Expr, vars: &[String], opts: Options) -> Result<SimplifyOutcome> {
    validate_var_count(vars)?;
    validate_bitwidth(opts.bitwidth)?;
    let sig = evaluate_boolean_signature(expr, vars.len() as u32, opts.bitwidth);
    simplify(&sig, vars, Some(expr), opts)
}

fn validate_public_inputs(sig: &[u64], vars: &[String], bitwidth: u32) -> Result<()> {
    validate_var_count(vars)?;
    validate_bitwidth(bitwidth)?;
    let expected_len = 1usize << vars.len();
    if sig.len() != expected_len {
        return Err(err(
            CobraError::InvalidArgument,
            format!(
                "signature length {} does not match 2^vars ({expected_len})",
                sig.len()
            ),
        ));
    }
    Ok(())
}

fn validate_var_count(vars: &[String]) -> Result<()> {
    if vars.len() > MAX_INPUT_VARS {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "Input variable count ({}) exceeds MAX_INPUT_VARS ({MAX_INPUT_VARS})",
                vars.len()
            ),
        ));
    }
    Ok(())
}

fn validate_bitwidth(bitwidth: u32) -> Result<()> {
    if !is_valid_bitwidth(bitwidth) {
        return Err(err(
            CobraError::InvalidArgument,
            format!("bitwidth must be in [1, 64]; got {bitwidth}"),
        ));
    }
    Ok(())
}

fn build_context(
    sig: &[u64],
    vars: &[String],
    input_expr: Option<&Expr>,
    opts: Options,
) -> OrchestratorContext {
    let bitwidth = opts.bitwidth;
    let mut ctx = OrchestratorContext::new(opts.clone(), vars.to_vec(), bitwidth);
    ctx.input_sig = sig.to_vec();
    ctx.evaluator = if opts.evaluator.has_body() {
        Some(opts.evaluator.with_trace(TraceKind::Root))
    } else {
        input_expr.map(|expr| Evaluator::from_expr(expr, bitwidth).with_trace(TraceKind::Root))
    };
    ctx
}

fn try_dynamic_mask(
    _sig: &[u64],
    vars: &[String],
    input_expr: &Expr,
    opts: &Options,
) -> Result<Option<SimplifyOutcome>> {
    let Some(mask) = detect_root_low_bit_mask(input_expr, opts.bitwidth) else {
        return Ok(None);
    };
    if contains_shr(mask.inner) {
        return Ok(None);
    }

    let inner = mask.inner.clone_tree();
    let eff_bw = mask.effective_width;
    let inner_sig = evaluate_boolean_signature(&inner, vars.len() as u32, eff_bw);
    let mut inner_opts = opts.clone();
    inner_opts.bitwidth = eff_bw;
    inner_opts.evaluator = Evaluator::default();

    let mut result = simplify(&inner_sig, vars, Some(&inner), inner_opts)?;
    if result.kind != SimplifyOutcomeKind::Simplified {
        return Ok(None);
    }

    let Some(inner_expr) = result.expr.take() else {
        return Ok(None);
    };
    let wrapped = Expr::and(inner_expr, Expr::constant(bitmask(eff_bw)));
    let eval = if opts.evaluator.has_body() {
        opts.evaluator.clone()
    } else {
        Evaluator::from_expr(input_expr, opts.bitwidth)
    };
    let check = verify_in_original_space(&eval, vars, &result.real_vars, &wrapped, opts.bitwidth);
    if !check.passed {
        return Ok(None);
    }

    result.sig_vector =
        evaluate_boolean_signature(&wrapped, result.real_vars.len() as u32, opts.bitwidth);
    result.expr = Some(wrapped);
    result.verified = true;
    Ok(Some(result))
}

fn try_no_ast_constant_seed(
    sig: &[u64],
    vars: &[String],
    ctx: &OrchestratorContext,
) -> Option<SimplifyOutcome> {
    let num_vars = vars.len() as u32;
    let candidate = match_pattern(sig, num_vars, ctx.bitwidth)?;
    if !matches!(candidate.kind, Kind::Constant(_)) {
        return None;
    }

    let mut verified = false;
    if let Some(eval) = ctx.evaluator.as_ref() {
        let check = full_width_check_eval(
            eval,
            num_vars,
            &candidate,
            ctx.bitwidth,
            DEFAULT_NUM_SAMPLES,
        );
        if !check.passed {
            return None;
        }
        verified = true;
    }

    Some(SimplifyOutcome {
        kind: SimplifyOutcomeKind::Simplified,
        expr: Some(candidate),
        sig_vector: sig.to_vec(),
        verified,
        ..SimplifyOutcome::default()
    })
}

fn seed_no_ast(
    sig: &[u64],
    vars: &[String],
    ctx: &mut OrchestratorContext,
    worklist: &mut Worklist,
) -> Result<()> {
    let elim = eliminate_aux_vars(sig, vars);
    if elim.real_vars.len() > ctx.opts.max_vars as usize {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "Variable count after elimination ({}) exceeds max_vars ({})",
                elim.real_vars.len(),
                ctx.opts.max_vars
            ),
        ));
    }

    let original_indices = cobra_core::expr_rewrite::build_var_support(vars, &elim.real_vars);
    let needs_original_space_verification = ctx.evaluator.is_some();
    let real_vars = elim.real_vars.clone();
    let payload = SignatureStatePayload {
        ctx: SignatureSubproblemContext {
            sig: sig.to_vec(),
            real_vars,
            elimination: elim,
            original_indices,
            needs_original_space_verification,
        },
    };
    let mut seed = WorkItem::new(StateData::Signature(Box::new(payload)));
    seed.features.provenance = Provenance::Original;
    if !needs_original_space_verification {
        seed.metadata.verification = VerificationState::Unverified;
    }
    let group_id = create_group(&mut ctx.competition_groups, &mut ctx.next_group_id, None);
    seed.group_id = Some(group_id);
    worklist.push(seed);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::{render, Kind};

    #[test]
    fn simplify_expr_runs_ast_pipeline() {
        let expr = Expr::add(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::mul(
                Expr::constant(2),
                Expr::and(Expr::variable(0), Expr::variable(1)),
            ),
        );
        let vars = vec!["x".to_string(), "y".to_string()];
        let outcome = simplify_expr(&expr, &vars, Options::default()).unwrap();
        assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
        assert!(outcome.verified);
        let rendered = render(outcome.expr.as_ref().unwrap(), &vars, 64);
        assert_eq!(rendered, "x + y");
    }

    #[test]
    fn simplify_rejects_invalid_public_inputs() {
        let vars = vec!["x".to_string()];
        let sig = vec![0, 1];
        let err = simplify(
            &sig,
            &vars,
            None,
            Options {
                bitwidth: 0,
                ..Options::default()
            },
        )
        .unwrap_err();
        assert_eq!(err.code, CobraError::InvalidArgument);

        let err = simplify(&[0], &vars, None, Options::default()).unwrap_err();
        assert_eq!(err.code, CobraError::InvalidArgument);
    }

    #[test]
    fn simplify_rejects_pathological_var_count() {
        let vars: Vec<String> = (0..=MAX_INPUT_VARS).map(|i| format!("v{i}")).collect();
        let err = simplify_expr(&Expr::constant(0), &vars, Options::default()).unwrap_err();
        assert_eq!(err.code, CobraError::TooManyVariables);
    }

    #[test]
    fn simplify_accepts_signature_only_input() {
        let vars = vec!["x".to_string(), "y".to_string()];
        let outcome = simplify(&[0, 1, 1, 0], &vars, None, Options::default()).unwrap();
        assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
        assert!(matches!(outcome.expr.unwrap().kind, Kind::Xor));
    }

    #[test]
    fn no_ast_constant_fast_path_is_unverified_without_evaluator() {
        let vars = vec!["x".to_string()];
        let outcome = simplify(&[7, 7], &vars, None, Options::default()).unwrap();
        assert_eq!(outcome.kind, SimplifyOutcomeKind::Simplified);
        assert!(!outcome.verified);
        assert!(matches!(outcome.expr.unwrap().kind, Kind::Constant(7)));
        assert_eq!(outcome.sig_vector, vec![7, 7]);
    }

    #[test]
    fn seed_no_ast_creates_signature_group() {
        let vars = vec!["x".to_string(), "y".to_string()];
        let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
        let mut worklist = Worklist::new();

        seed_no_ast(&[0, 1, 1, 2], &vars, &mut ctx, &mut worklist).unwrap();

        let item = worklist.pop().expect("signature seed");
        assert!(matches!(item.payload, StateData::Signature(_)));
        assert_eq!(item.group_id, Some(0));
        assert_eq!(ctx.next_group_id, 1);
        assert_eq!(ctx.competition_groups[&0].open_handles, 1);
    }
}
