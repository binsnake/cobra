//! Public simplifier entry points that own seeding plus orchestrator dispatch.
//!
//! This is the Rust equivalent of upstream `Simplify`: validate public inputs,
//! seed either from an AST or from a Boolean signature, then run the pass
//! registry to a [`crate::core::simplify_outcome::SimplifyOutcome`].

use crate::core::arith::bitmask;
use crate::core::evaluator::{Evaluator, TraceKind};
use crate::core::expr::{Expr, Kind};
use crate::core::pass_contract::VerificationState;
use crate::core::result::{err, CobraError, Result};
use crate::core::simplify_outcome::ProofLevel;
use crate::core::simplify_outcome::{Options, SimplifyOutcome, SimplifyOutcomeKind};
use crate::core::{evaluate_boolean_signature, is_valid_bitwidth};
use crate::ir::{contains_shr, detect_root_low_bit_mask};

use crate::orchestrator::{
    create_group, simplify_from_worklist, OrchestratorContext, OrchestratorPolicy, Provenance,
    SignatureStatePayload, SignatureSubproblemContext, StateData, WorkItem, Worklist,
};

use crate::passes::aux_var::eliminate_aux_vars;
use crate::passes::pattern_matcher::match_pattern;
use crate::passes::seed::seed_with_ast;
use crate::passes::spot_check::{
    full_width_check_eval, verify_in_original_space, DEFAULT_NUM_SAMPLES,
};
use crate::passes::PASS_REGISTRY;

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
    ctx.original_expr = input_expr.map(Expr::clone_tree);
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
    result.verified = false;
    result.proof_level = ProofLevel::Unverified;
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
    }

    Some(SimplifyOutcome {
        kind: SimplifyOutcomeKind::Simplified,
        expr: Some(candidate),
        sig_vector: sig.to_vec(),
        verified: false,
        proof_level: ProofLevel::Unverified,
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

    let original_indices = crate::core::expr_rewrite::build_var_support(vars, &elim.real_vars);
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
    use crate::core::expr::{render, Kind};

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

    // --- Mixed-width soundness (the wall) --------------------------------

    /// Sample-check that `simplify_expr`'s output is semantically equivalent
    /// to its input over `bitwidth`-wide variable assignments.
    fn assert_simplify_preserves_semantics(expr: &Expr, vars: &[String], bitwidth: u32) {
        let outcome = simplify_expr(expr, vars, Options::default())
            .expect("simplify must not error on a well-formed mixed-width expr");
        // The wall may legitimately leave it unchanged/unsupported; whatever
        // comes back must still compute the same value as the input.
        let Some(result) = outcome.expr.as_ref() else {
            return;
        };
        let input_eval = Evaluator::from_expr(expr, bitwidth);
        let output_eval = Evaluator::from_expr(result, bitwidth);
        let n = vars.len();
        // Deterministic spread of assignments across the variable space.
        for seed in 0u64..64 {
            let point: Vec<u64> = (0..n)
                .map(|i| {
                    let rot = u32::try_from(i * 7 + 3).unwrap_or(0) & 63;
                    seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(rot)
                })
                .collect();
            assert_eq!(
                input_eval.eval(&point),
                output_eval.eval(&point),
                "mixed-width simplify changed semantics at {point:?}"
            );
        }
    }

    #[test]
    fn mixed_width_zext_is_handled_soundly() {
        // zext(v0, 32) is non-uniform: the pipeline must wall it off and
        // never panic (the bit_partitioner tripwire) nor miscompile.
        let expr = Expr::zext(Expr::variable(0), 32);
        let vars = vec!["a".to_string()];
        assert_simplify_preserves_semantics(&expr, &vars, 64);
    }

    #[test]
    fn mixed_width_concat_is_handled_soundly() {
        // concat(v0:u8, v1:u8) — a width-summing node buried in arithmetic.
        let expr = Expr::add(
            Expr::concat(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let vars = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        assert_simplify_preserves_semantics(&expr, &vars, 64);
    }

    #[test]
    fn mixed_width_cast_inside_mba_stays_equivalent() {
        // A cross-width MBA: trunc inside a bitwise/arith mix. The opaque
        // path must keep it equivalent (output == input semantically).
        let expr = Expr::xor(
            Expr::trunc(Expr::variable(0), 8),
            Expr::and(Expr::variable(1), Expr::constant(0xFF)),
        );
        let vars = vec!["a".to_string(), "b".to_string()];
        assert_simplify_preserves_semantics(&expr, &vars, 64);
    }

    // --- Shift still works (parse -> simplify) ---------------------------

    #[test]
    fn shl_parses_to_mul_and_simplifies_sanely() {
        // `a << 3` lowers to `a * 8` at parse; simplify must keep it
        // semantically equal to the input.
        let parsed = crate::parser::parse_to_ast("a << 3", 64).expect("parse a << 3");
        assert!(
            matches!(parsed.expr.kind, Kind::Mul),
            "a << 3 should lower to a Mul node"
        );
        assert_simplify_preserves_semantics(&parsed.expr, &parsed.vars, 64);
    }

    #[test]
    fn shr_parses_to_shr_node_and_simplifies_sanely() {
        // `a >> 2` stays a Shr(2) node; simplify must keep it equivalent.
        let parsed = crate::parser::parse_to_ast("a >> 2", 64).expect("parse a >> 2");
        match parsed.expr.kind {
            Kind::Shr(k) => assert_eq!(k, 2),
            ref other => panic!("a >> 2 should be Shr(2), got {other:?}"),
        }
        assert_simplify_preserves_semantics(&parsed.expr, &parsed.vars, 64);
    }
}
