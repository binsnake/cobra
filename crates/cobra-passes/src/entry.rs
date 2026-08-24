//! Public simplifier entry points that own seeding plus orchestrator dispatch.
//!
//! This is the Rust equivalent of upstream `Simplify`: validate public inputs,
//! seed either from an AST or from a Boolean signature, then run the pass
//! registry to a [`crate::core::simplify_outcome::SimplifyOutcome`].

use crate::core::arith::bitmask;
use crate::core::evaluator::{Evaluator, TraceKind};
use crate::core::expr::{Expr, Kind};
use crate::core::expr_cost::{compute_cost, is_better};
use crate::core::pass_contract::{PassOutcome, VerificationState};
use crate::core::result::{err, CobraError, Result};
use crate::core::simplify_outcome::ProofLevel;
use crate::core::simplify_outcome::{Options, SimplifyOutcome, SimplifyOutcomeKind};
use crate::core::{
    checked_signature_len, evaluate_boolean_signature, is_valid_bitwidth,
    try_evaluate_boolean_signature, validate_widths, MAX_SIGNATURE_VARS,
};
use crate::ir::{contains_shr, detect_root_low_bit_mask};

use crate::orchestrator::{
    create_group, run_main_loop, to_simplify_outcome, OrchestratorContext, OrchestratorPolicy,
    Provenance, SignatureStatePayload, SignatureSubproblemContext, StateData, WorkItem, Worklist,
};

use crate::passes::aux_var::eliminate_aux_vars;
use crate::passes::pattern_matcher::{match_pattern, simplify_xor_chains};
use crate::passes::seed::seed_with_ast;
use crate::passes::spot_check::{
    full_width_check_eval, verify_in_original_space, DEFAULT_NUM_SAMPLES,
};
use crate::passes::PASS_REGISTRY;

/// Upper bound checked before any `2^vars.len()` signature allocation.
pub const MAX_INPUT_VARS: usize = MAX_SIGNATURE_VARS as usize;
const MAX_EXPRESSION_DEPTH: usize = 512;
const MAX_LOGICAL_NODES: usize = 100_000;

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
    validate_public_inputs(sig, vars, opts.bitwidth, opts.max_vars)?;

    if let Some(expr) = input_expr {
        validate_expr_input(expr, vars, opts.bitwidth)?;
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

    let mut policy = OrchestratorPolicy::default();
    let mut loop_result = run_main_loop(
        &mut ctx,
        &mut worklist,
        &mut policy,
        PASS_REGISTRY,
        input_expr,
    )?;

    // Exact exhaustion fallback from upstream v1.3: flatten XOR chains and
    // remove operands with even multiplicity (`T ^ T == 0`). A surviving
    // operand can have a degenerate Boolean signature, leaving every normal
    // solver path exhausted even though the raw AST has a much cheaper exact
    // form. Restrict this to unsupported AST-backed runs, require a strict
    // cost improvement, and retain the full-width check as defense in depth.
    // This deliberately runs on the raw exhausted-loop result, before public
    // conversion. A successful candidate that is later rejected by the global
    // cost or lifted-variable guards must not be mistaken for exhaustion.
    if !loop_result.outcome.succeeded() {
        if let (Some(expr), Some(eval)) = (input_expr, ctx.evaluator.as_ref()) {
            if contains_xor(expr) {
                let peeled = simplify_xor_chains(expr.clone_tree(), ctx.bitwidth);
                if *peeled != *expr
                    && is_better(&compute_cost(&peeled).cost, &compute_cost(expr).cost)
                    && full_width_check_eval(
                        eval,
                        vars.len() as u32,
                        &peeled,
                        ctx.bitwidth,
                        DEFAULT_NUM_SAMPLES,
                    )
                    .passed
                {
                    let peeled_sig =
                        evaluate_boolean_signature(&peeled, vars.len() as u32, ctx.bitwidth);
                    loop_result.outcome =
                        PassOutcome::success(peeled, vars.to_vec(), VerificationState::Verified);
                    loop_result.metadata.verification = VerificationState::Verified;
                    loop_result.metadata.sig_vector = peeled_sig;
                    loop_result.metadata.candidate_failed_verification = false;
                    loop_result.metadata.reason_code = None;
                    loop_result.metadata.cause_chain.clear();
                    loop_result.metadata.lean_certificate = None;
                    loop_result.metadata.lean_signature_certificate = None;
                }
            }
        }
    }

    let require_lean_certificate = ctx.opts.require_lean_certificate;
    Ok(to_simplify_outcome(
        loop_result,
        input_expr,
        ctx.bitwidth,
        &ctx.original_vars,
        require_lean_certificate,
    ))
}

fn contains_xor(expr: &Expr) -> bool {
    matches!(expr.kind, Kind::Xor) || expr.children.iter().any(|child| contains_xor(child))
}

/// Convenience wrapper for callers that have an AST and want the Boolean
/// signature computed from it.
pub fn simplify_expr(expr: &Expr, vars: &[String], opts: Options) -> Result<SimplifyOutcome> {
    validate_var_count(vars, opts.max_vars)?;
    validate_bitwidth(opts.bitwidth)?;
    validate_unique_var_names(vars)?;
    validate_expr_input(expr, vars, opts.bitwidth)?;
    let sig = try_evaluate_boolean_signature(expr, vars.len() as u32, opts.bitwidth)?;
    simplify(&sig, vars, Some(expr), opts)
}

fn validate_public_inputs(
    sig: &[u64],
    vars: &[String],
    bitwidth: u32,
    configured_max: u32,
) -> Result<()> {
    validate_var_count(vars, configured_max)?;
    validate_bitwidth(bitwidth)?;
    validate_unique_var_names(vars)?;
    let expected_len = checked_signature_len(vars.len() as u32)?;
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

fn validate_var_count(vars: &[String], configured_max: u32) -> Result<()> {
    let limit = MAX_INPUT_VARS.min(configured_max as usize);
    if vars.len() > limit {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "Input variable count ({}) exceeds configured safe limit ({limit})",
                vars.len()
            ),
        ));
    }
    Ok(())
}

fn validate_unique_var_names(vars: &[String]) -> Result<()> {
    let mut seen = std::collections::HashSet::with_capacity(vars.len());
    for name in vars {
        if !seen.insert(name.as_str()) {
            return Err(err(
                CobraError::InvalidArgument,
                format!("duplicate variable name: {name}"),
            ));
        }
    }
    Ok(())
}

fn validate_expr_input(expr: &Expr, vars: &[String], bitwidth: u32) -> Result<()> {
    let mut stack = vec![(expr, 1usize)];
    let mut logical_nodes = 0usize;
    while let Some((node, depth)) = stack.pop() {
        logical_nodes = logical_nodes.checked_add(1).ok_or_else(|| {
            err(
                CobraError::InvalidArgument,
                "expression logical node count overflow",
            )
        })?;
        if logical_nodes > MAX_LOGICAL_NODES {
            return Err(err(
                CobraError::InvalidArgument,
                format!("expression exceeds logical node budget {MAX_LOGICAL_NODES}"),
            ));
        }
        if depth > MAX_EXPRESSION_DEPTH {
            return Err(err(
                CobraError::InvalidArgument,
                format!("expression exceeds depth budget {MAX_EXPRESSION_DEPTH}"),
            ));
        }
        if let Kind::Variable(index) = node.kind {
            if index as usize >= vars.len() {
                return Err(err(
                    CobraError::InvalidArgument,
                    format!("variable index {index} has no corresponding name"),
                ));
            }
        }
        for child in &node.children {
            // An associative chain is not nesting. `Expr::add` is binary, so a
            // flat N-addend sum is an N-deep left spine and a 512-term sum
            // tripped the depth budget before a single pass ran -- while
            // MAX_LOGICAL_NODES (100_000) was 50x from firing, making the two
            // budgets mutually inconsistent for chain-shaped input. Only count
            // a step when the operator actually changes.
            let child_depth = if is_associative_chain_step(&node.kind, &child.kind) {
                depth
            } else {
                depth + 1
            };
            stack.push((child, child_depth));
        }
    }
    validate_widths(expr, &[], bitwidth)
}

/// `true` when descending from `parent` into `child` continues one flat
/// associative chain rather than nesting a new operator.
fn is_associative_chain_step(parent: &Kind, child: &Kind) -> bool {
    matches!(
        parent,
        Kind::Add | Kind::Mul | Kind::And | Kind::Or | Kind::Xor
    ) && parent == child
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
    fn boolean_signature_only_product_rewrite_cannot_replace_original_ast() {
        fn equals_hidden_value(var: u32, a: u64, b: u64) -> std::sync::Arc<Expr> {
            let target = Expr::mul(Expr::constant(a), Expr::constant(b));
            let delta = Expr::xor(Expr::variable(var), target);
            let nonzero = Expr::or(delta.clone_tree(), Expr::neg(delta));
            Expr::shr(Expr::not(nonzero), 63)
        }

        let a = 0x12345;
        let b = 0x10001;
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let hidden = equals_hidden_value(0, a, b);
        let original = Expr::add(
            Expr::mul(
                Expr::add(Expr::and(x.clone_tree(), y.clone_tree()), hidden),
                Expr::or(x.clone_tree(), y.clone_tree()),
            ),
            Expr::mul(
                Expr::and(x.clone_tree(), Expr::not(y.clone_tree())),
                Expr::and(Expr::not(x), y),
            ),
        );
        let outcome = simplify_expr(
            &original,
            &["x".to_owned(), "y".to_owned()],
            Options::default(),
        )
        .expect("simplification must fail closed, not error");
        assert_eq!(outcome.expr, Some(original));
        assert!(!outcome.verified);
        assert_eq!(outcome.proof_level, ProofLevel::Unverified);
    }

    #[test]
    fn xor_chain_exhaustion_fallback_cancels_complex_duplicate() {
        let survivor = || {
            Expr::or(
                Expr::and(
                    Expr::add(Expr::variable(0), Expr::variable(1)),
                    Expr::variable(2),
                ),
                Expr::constant(3),
            )
        };
        let duplicate = || {
            Expr::add(
                Expr::or(
                    Expr::mul(Expr::variable(0), Expr::variable(2)),
                    Expr::and(Expr::variable(1), Expr::constant(85)),
                ),
                Expr::variable(3),
            )
        };
        let input = Expr::xor(Expr::xor(survivor(), duplicate()), duplicate());
        let vars = ["x", "y", "z", "w"].map(str::to_string);

        let outcome = simplify_expr(&input, &vars, Options::default()).expect("simplify");
        assert_eq!(outcome.kind, SimplifyOutcomeKind::UnchangedUnsupported);
        assert_eq!(outcome.expr, Some(input));
        assert_eq!(outcome.proof_level, ProofLevel::Unverified);
        assert!(!outcome.verified);
        assert!(outcome.diag.reason.contains("replayable proof"));
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
    fn simplify_rejects_duplicate_variable_names_without_panicking() {
        let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
        let error = simplify_expr(&expr, &["x".to_owned(), "x".to_owned()], Options::default())
            .expect_err("duplicate names must be rejected");
        assert_eq!(error.code, CobraError::InvalidArgument);
        assert!(error.message.contains("duplicate variable name"));
    }

    #[test]
    fn simplify_applies_configured_var_limit_before_signature_work() {
        let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
        let error = simplify_expr(
            &expr,
            &["x".to_owned(), "y".to_owned()],
            Options {
                max_vars: 1,
                ..Options::default()
            },
        )
        .expect_err("configured limit must fail before signature construction");
        assert_eq!(error.code, CobraError::TooManyVariables);
    }

    #[test]
    fn simplify_rejects_invalid_width_and_excessive_depth() {
        let error = simplify_expr(
            &Expr::zext(Expr::variable(0), 65),
            &["x".to_owned()],
            Options::default(),
        )
        .expect_err("widths above u64 capacity must be rejected");
        assert_eq!(error.code, CobraError::InvalidArgument);

        let mut deep = Expr::variable(0);
        for _ in 0..MAX_EXPRESSION_DEPTH {
            deep = Expr::not(deep);
        }
        let error = simplify_expr(&deep, &["x".to_owned()], Options::default())
            .expect_err("excessive depth must be rejected before recursive walkers");
        assert_eq!(error.code, CobraError::InvalidArgument);
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
        // Non-uniform but well-formed: narrow to 8 bits, then widen to 32.
        // The pipeline must wall it off and never panic (the bit_partitioner
        // tripwire) nor miscompile.
        let expr = Expr::zext(Expr::trunc(Expr::variable(0), 8), 32);
        let vars = vec!["a".to_string()];
        assert_simplify_preserves_semantics(&expr, &vars, 64);
    }

    #[test]
    fn narrowing_cast_is_rejected_at_public_boundary() {
        // `zext(v0, 32)` over a 64-bit variable is a narrowing extension: the
        // evaluator masks it down while the name says widen, and the two
        // disagree once it reaches a solver. Reject it as malformed IR.
        let vars = vec!["a".to_string()];
        let narrowing_zext = Expr::zext(Expr::variable(0), 32);
        assert!(simplify_expr(&narrowing_zext, &vars, Options::default()).is_err());

        // The dual: a truncation wider than its child.
        let widening_trunc = Expr::trunc(Expr::zext(Expr::variable(0), 64), 64);
        assert!(simplify_expr(&widening_trunc, &vars, Options::default()).is_ok());
    }

    #[test]
    fn oversized_concat_is_rejected_at_public_boundary() {
        // Bare variables are 64-bit, so their concatenation cannot be
        // represented by the public u64 evaluator.
        let expr = Expr::add(
            Expr::concat(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let vars = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let error = simplify_expr(&expr, &vars, Options::default())
            .expect_err("128-bit concatenation must fail closed");
        assert_eq!(error.code, CobraError::InvalidArgument);
    }

    #[test]
    fn mixed_width_cast_inside_mba_stays_equivalent() {
        // A cross-width MBA: trunc inside a bitwise/arith mix. The opaque
        // path must keep it equivalent (output == input semantically).
        let expr = Expr::xor(
            Expr::trunc(Expr::variable(0), 8),
            Expr::and(
                Expr::trunc(Expr::variable(1), 8),
                Expr::trunc(Expr::constant(0xFF), 8),
            ),
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
