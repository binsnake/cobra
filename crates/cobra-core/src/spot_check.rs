//! Spot-check verification: compare a simplified `Expr` against an
//! `Evaluator` at a curated set of probe points. Ported from
//! `lib/core/SignatureChecker.cpp`'s `FullWidthCheckEval`.
//!
//! This initial port covers adversarial single-value and per-variable
//! probes plus a small random sample. The expression-derived-constant
//! Phase 3/4 and the two-variable combinations (Phase 5) are deferred
//! to a later pass together with the full `SignatureChecker` API.

use crate::arith::bitmask;
use crate::compiled::{compile, eval as eval_compiled, CompiledExpr};
use crate::evaluator::{Evaluator, Workspace};
use crate::expr::Expr;
use crate::expr_utils::remap_var_indices;

/// Matches C++ `CheckResult`. `failing_input` is populated with the
/// inputs that produced a disagreement (when `passed == false`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckResult {
    pub passed: bool,
    pub failing_input: Vec<u64>,
}

/// `num_samples` mirrors the C++ default — used for the random phase.
pub const DEFAULT_NUM_SAMPLES: u32 = 8;

/// Compare `simplified` against `eval_original` at a curated probe set
/// (adversarial values and random samples). Short-circuits and returns
/// the failing input on the first disagreement.
#[must_use]
pub fn full_width_check_eval(
    eval_original: &Evaluator,
    num_vars: u32,
    simplified: &Expr,
    bitwidth: u32,
    num_samples: u32,
) -> CheckResult {
    let mask = bitmask(bitwidth);
    let simplified_prog = compile(simplified, bitwidth);

    // Reject expressions wider than the caller's variable space — matches
    // the C++ arity guard.
    let original_arity = if eval_original.has_compiled() {
        eval_original.input_arity()
    } else {
        0
    };
    if original_arity > num_vars || simplified_prog.arity > num_vars {
        return CheckResult::default();
    }

    let mut inputs = vec![0u64; num_vars as usize];
    let mut simplified_stack: Vec<u64> = Vec::with_capacity(simplified_prog.stack_size);
    let mut original_workspace = Workspace::default();

    // Phase 1: adversarial broadcast — all vars share a single value.
    for val in adversarial_values(bitwidth) {
        inputs.fill(val);
        if let Some(fail) = probe_point(
            eval_original,
            &simplified_prog,
            &inputs,
            mask,
            &mut original_workspace,
            &mut simplified_stack,
        ) {
            return CheckResult {
                passed: false,
                failing_input: fail,
            };
        }
    }

    // Phase 2: adversarial per-variable — single var set, rest zero.
    for v in 0..num_vars as usize {
        for val in adversarial_values(bitwidth) {
            inputs.fill(0);
            if let Some(slot) = inputs.get_mut(v) {
                *slot = val;
            }
            if let Some(fail) = probe_point(
                eval_original,
                &simplified_prog,
                &inputs,
                mask,
                &mut original_workspace,
                &mut simplified_stack,
            ) {
                return CheckResult {
                    passed: false,
                    failing_input: fail,
                };
            }
        }
    }

    // Phase 3: random samples using a deterministic SplitMix64 stream
    // seeded from `(num_vars, bitwidth, num_samples)`. Not byte-for-byte
    // with the C++ PRNG but offers the same coverage intent.
    let mut rng_state = seed_for(num_vars, bitwidth, num_samples);
    for _ in 0..num_samples {
        for slot in &mut inputs {
            *slot = splitmix64(&mut rng_state) & mask;
        }
        if let Some(fail) = probe_point(
            eval_original,
            &simplified_prog,
            &inputs,
            mask,
            &mut original_workspace,
            &mut simplified_stack,
        ) {
            return CheckResult {
                passed: false,
                failing_input: fail,
            };
        }
    }

    CheckResult {
        passed: true,
        failing_input: Vec::new(),
    }
}

/// `VerifyInOriginalSpace`: when the simplified expression is in a
/// reduced variable space (`real_vars` subset of `all_vars`), remap its
/// var indices into the original space and then spot-check.
#[must_use]
pub fn verify_in_original_space(
    eval: &Evaluator,
    all_vars: &[String],
    real_vars: &[String],
    reduced_expr: &Expr,
    bitwidth: u32,
) -> CheckResult {
    let all_count = all_vars.len() as u32;
    if real_vars.is_empty() || real_vars.len() == all_vars.len() {
        return full_width_check_eval(eval, all_count, reduced_expr, bitwidth, DEFAULT_NUM_SAMPLES);
    }
    // When `real_vars` lives in a namespace other than `all_vars`
    // (residual / lifted-outer candidates), we can't remap. Report
    // the check as failed so the caller routes this candidate
    // through the group resolver rather than crashing.
    let Some(idx_map) = crate::expr_rewrite::try_build_var_support(all_vars, real_vars) else {
        return CheckResult::default();
    };
    let mut remapped = reduced_expr.clone();
    remap_var_indices(&mut remapped, &idx_map);
    full_width_check_eval(eval, all_count, &remapped, bitwidth, DEFAULT_NUM_SAMPLES)
}

fn probe_point(
    eval_original: &Evaluator,
    simplified_prog: &CompiledExpr,
    inputs: &[u64],
    mask: u64,
    original_workspace: &mut Workspace,
    simplified_stack: &mut Vec<u64>,
) -> Option<Vec<u64>> {
    let original_val = if eval_original.has_compiled() {
        eval_original.eval_with(inputs, original_workspace) & mask
    } else {
        eval_original.eval(inputs) & mask
    };
    let simplified_val = eval_compiled(simplified_prog, inputs, simplified_stack);
    if original_val == simplified_val {
        None
    } else {
        Some(inputs.to_vec())
    }
}

/// Small curated set of "interesting" values: 0, 1, -1, -2, -3, -4,
/// 2^k-1 / 2^k / 2^k+1 for each bit position, plus 3/5/7 and the
/// alternating bit patterns 0x5555... / 0xAAAA... Matches the C++
/// `BuildAdversarialValues` closely (minus bitwidth-dependent dedup
/// ordering — we dedupe on the fly).
fn adversarial_values(bitwidth: u32) -> Vec<u64> {
    let mask = bitmask(bitwidth);
    let mut vals: Vec<u64> = Vec::with_capacity(4 * bitwidth as usize + 16);
    let push = |vals: &mut Vec<u64>, v: u64| vals.push(v & mask);

    push(&mut vals, 0);
    push(&mut vals, 1);
    push(&mut vals, mask); // -1
    push(&mut vals, mask.wrapping_sub(1));
    push(&mut vals, mask.wrapping_sub(2));
    push(&mut vals, mask.wrapping_sub(3));

    for k in 1..bitwidth {
        let pow = 1u64 << k;
        push(&mut vals, pow.wrapping_sub(1));
        push(&mut vals, pow);
        if k + 1 < bitwidth {
            push(&mut vals, pow.wrapping_add(1));
        }
    }
    push(&mut vals, 3);
    push(&mut vals, 5);
    push(&mut vals, 7);
    push(&mut vals, 0x5555_5555_5555_5555 & mask);
    push(&mut vals, 0xAAAA_AAAA_AAAA_AAAA & mask);

    vals.sort_unstable();
    vals.dedup();
    vals
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn seed_for(num_vars: u32, bitwidth: u32, num_samples: u32) -> u64 {
    (u64::from(num_vars)).wrapping_mul(2_654_435_761)
        ^ (u64::from(bitwidth)).wrapping_mul(40_503)
        ^ (u64::from(num_samples)).wrapping_mul(0xDEAD_BEEF)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equivalent_expressions_pass() {
        // x + y vs y + x — commutative, must pass.
        let original = Expr::add(Expr::variable(0), Expr::variable(1));
        let simplified = Expr::add(Expr::variable(1), Expr::variable(0));
        let eval = Evaluator::from_expr(&original, 64);
        let r = full_width_check_eval(&eval, 2, &simplified, 64, DEFAULT_NUM_SAMPLES);
        assert!(r.passed, "commutative Add should match: {r:?}");
        assert!(r.failing_input.is_empty());
    }

    #[test]
    fn non_equivalent_expressions_fail_with_counterexample() {
        // x + y vs x * y — differ at (2, 3): 5 vs 6.
        let original = Expr::add(Expr::variable(0), Expr::variable(1));
        let simplified = Expr::mul(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&original, 64);
        let r = full_width_check_eval(&eval, 2, &simplified, 64, DEFAULT_NUM_SAMPLES);
        assert!(!r.passed);
        assert_eq!(r.failing_input.len(), 2);
    }

    #[test]
    fn mba_identity_verifies_via_spot_check() {
        // (x & y) + (x | y) == x + y
        let original = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let simplified = Expr::add(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&original, 64);
        let r = full_width_check_eval(&eval, 2, &simplified, 64, DEFAULT_NUM_SAMPLES);
        assert!(r.passed);
    }

    #[test]
    fn verify_in_original_space_handles_var_remapping() {
        // All-vars = [a, b, c]; simplified lives in {a, c} space.
        // Simplified = x + y (over [a, c]) needs remap: var0 → 0, var1 → 2.
        let all = vec!["a".into(), "b".into(), "c".into()];
        let real = vec!["a".into(), "c".into()];
        let original = Expr::add(Expr::variable(0), Expr::variable(2));
        let eval = Evaluator::from_expr(&original, 64);
        let reduced_expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let r = verify_in_original_space(&eval, &all, &real, &reduced_expr, 64);
        assert!(r.passed, "remapped spot-check should pass: {r:?}");
    }
}
