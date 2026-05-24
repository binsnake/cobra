//! Signature and spot-check verification for simplified expressions.
//!
//! Full-width checks run the upstream probe schedule: adversarial values,
//! expression-derived constants, two-variable constant combinations, and a
//! deterministic random sample.

use crate::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr};
use crate::compiled::{compile, eval as eval_compiled, CompiledExpr};
use crate::evaluator::{Evaluator, Workspace};
use crate::expr::{Expr, Kind};
use crate::expr_utils::remap_var_indices;
use crate::signature_eval::evaluate_boolean_signature;

/// inputs that produced a disagreement (when `passed == false`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckResult {
    pub passed: bool,
    pub failing_input: Vec<u64>,
}

pub const DEFAULT_NUM_SAMPLES: u32 = 8;
pub const RESIDUAL_GATE_NUM_SAMPLES: u32 = 64;

/// Verify that `simplified` matches `original_sig` on all Boolean inputs.
#[must_use]
pub fn signature_check(
    original_sig: &[u64],
    simplified: &Expr,
    num_vars: u32,
    bitwidth: u32,
) -> CheckResult {
    let computed = evaluate_boolean_signature(simplified, num_vars, bitwidth);
    let mask = bitmask(bitwidth);
    let len = 1usize << num_vars;
    if original_sig.len() < len || computed.len() < len {
        return CheckResult::default();
    }

    for i in 0..len {
        if computed[i] != (original_sig[i] & mask) {
            let mut failing_input = vec![0u64; num_vars as usize];
            for (v, slot) in failing_input.iter_mut().enumerate() {
                *slot = ((i >> v) & 1) as u64;
            }
            return CheckResult {
                passed: false,
                failing_input,
            };
        }
    }

    CheckResult {
        passed: true,
        failing_input: Vec::new(),
    }
}

/// Compare `simplified` against `original` at full-width probe points.
///
/// `var_map` maps simplified variable indices to original variable indices.
/// If empty, an identity mapping is used.
#[must_use]
pub fn full_width_check(
    original: &Expr,
    original_num_vars: u32,
    simplified: &Expr,
    var_map: &[u32],
    bitwidth: u32,
    num_samples: u32,
) -> CheckResult {
    let original_prog = compile(original, bitwidth);
    let simplified_prog = compile(simplified, bitwidth);
    let simplified_num_vars = if var_map.is_empty() {
        original_num_vars
    } else {
        var_map.len() as u32
    };

    if original_prog.arity > original_num_vars || simplified_prog.arity > simplified_num_vars {
        return CheckResult::default();
    }

    let expr_constants = build_expr_derived_probes(Some(original), Some(simplified), bitwidth);
    let mut original_stack = Vec::with_capacity(original_prog.stack_size);
    let mut simplified_stack = Vec::with_capacity(simplified_prog.stack_size);
    let mut simplified_inputs = vec![0u64; simplified_num_vars as usize];

    let failing = for_each_full_width_probe(
        original_num_vars,
        bitwidth,
        num_samples,
        &expr_constants,
        |original_inputs| {
            for (v, slot) in simplified_inputs.iter_mut().enumerate() {
                let original_index = if var_map.is_empty() {
                    v
                } else {
                    var_map[v] as usize
                };
                let Some(value) = original_inputs.get(original_index) else {
                    return false;
                };
                *slot = *value;
            }
            eval_compiled(&original_prog, original_inputs, &mut original_stack)
                == eval_compiled(&simplified_prog, &simplified_inputs, &mut simplified_stack)
        },
    );

    match failing {
        Some(failing_input) => CheckResult {
            passed: false,
            failing_input,
        },
        None => CheckResult {
            passed: true,
            failing_input: Vec::new(),
        },
    }
}

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

    let expr_constants = build_expr_derived_probes(None, Some(simplified), bitwidth);
    let mut simplified_stack: Vec<u64> = Vec::with_capacity(simplified_prog.stack_size);
    let mut original_workspace = Workspace::default();

    let failing =
        for_each_full_width_probe(num_vars, bitwidth, num_samples, &expr_constants, |inputs| {
            probe_point(
                eval_original,
                &simplified_prog,
                inputs,
                mask,
                &mut original_workspace,
                &mut simplified_stack,
            )
            .is_none()
        });

    match failing {
        Some(failing_input) => CheckResult {
            passed: false,
            failing_input,
        },
        None => CheckResult {
            passed: true,
            failing_input: Vec::new(),
        },
    }
}

/// Evaluate an expression at the provided variable values.
#[must_use]
pub fn eval_expr(expr: &Expr, var_values: &[u64], bitwidth: u32) -> u64 {
    let mask = bitmask(bitwidth);
    match &expr.kind {
        Kind::Constant(v) => *v & mask,
        Kind::Variable(index) => var_values[*index as usize] & mask,
        Kind::Add => mod_add(
            eval_expr(&expr.children[0], var_values, bitwidth),
            eval_expr(&expr.children[1], var_values, bitwidth),
            bitwidth,
        ),
        Kind::Mul => mod_mul(
            eval_expr(&expr.children[0], var_values, bitwidth),
            eval_expr(&expr.children[1], var_values, bitwidth),
            bitwidth,
        ),
        Kind::And => {
            (eval_expr(&expr.children[0], var_values, bitwidth)
                & eval_expr(&expr.children[1], var_values, bitwidth))
                & mask
        }
        Kind::Or => {
            (eval_expr(&expr.children[0], var_values, bitwidth)
                | eval_expr(&expr.children[1], var_values, bitwidth))
                & mask
        }
        Kind::Xor => {
            (eval_expr(&expr.children[0], var_values, bitwidth)
                ^ eval_expr(&expr.children[1], var_values, bitwidth))
                & mask
        }
        Kind::Not => mod_not(eval_expr(&expr.children[0], var_values, bitwidth), bitwidth),
        Kind::Neg => mod_neg(eval_expr(&expr.children[0], var_values, bitwidth), bitwidth),
        Kind::Shr(amount) => mod_shr(
            eval_expr(&expr.children[0], var_values, bitwidth),
            u64::from(*amount),
            bitwidth,
        ),
    }
}

fn for_each_full_width_probe(
    num_vars: u32,
    bitwidth: u32,
    num_samples: u32,
    expr_constants: &[u64],
    mut probe_fn: impl FnMut(&[u64]) -> bool,
) -> Option<Vec<u64>> {
    let mask = bitmask(bitwidth);
    let mut inputs = vec![0u64; num_vars as usize];

    for val in adversarial_values(bitwidth) {
        inputs.fill(val);
        if !probe_fn(&inputs) {
            return Some(inputs.clone());
        }
    }

    for v in 0..num_vars as usize {
        for val in adversarial_values(bitwidth) {
            inputs.fill(0);
            inputs[v] = val;
            if !probe_fn(&inputs) {
                return Some(inputs.clone());
            }
        }
    }

    for &val in expr_constants {
        inputs.fill(val);
        if !probe_fn(&inputs) {
            return Some(inputs.clone());
        }
    }

    for v in 0..num_vars as usize {
        for &val in expr_constants {
            inputs.fill(0);
            inputs[v] = val;
            if !probe_fn(&inputs) {
                return Some(inputs.clone());
            }
        }
    }

    if num_vars >= 2 && expr_constants.len() >= 2 {
        let mut probes = 0usize;
        'pairs: for va in 0..num_vars as usize {
            for vb in (va + 1)..num_vars as usize {
                for ci in 0..expr_constants.len() {
                    for cj in (ci + 1)..expr_constants.len() {
                        inputs.fill(0);
                        inputs[va] = expr_constants[ci];
                        inputs[vb] = expr_constants[cj];
                        if !probe_fn(&inputs) {
                            return Some(inputs.clone());
                        }

                        inputs[va] = expr_constants[cj];
                        inputs[vb] = expr_constants[ci];
                        if !probe_fn(&inputs) {
                            return Some(inputs.clone());
                        }

                        probes += 2;
                        if probes >= 64 {
                            break 'pairs;
                        }
                    }
                }
            }
        }
    }

    let mut rng_state = seed_for(num_vars, bitwidth, num_samples);
    for _ in 0..num_samples {
        for slot in &mut inputs {
            *slot = splitmix64(&mut rng_state) & mask;
        }
        if !probe_fn(&inputs) {
            return Some(inputs.clone());
        }
    }

    None
}

fn build_expr_derived_probes(
    expr_a: Option<&Expr>,
    expr_b: Option<&Expr>,
    bitwidth: u32,
) -> Vec<u64> {
    let mask = bitmask(bitwidth);
    let mut raw = Vec::new();
    let mut shifts = Vec::new();
    if let Some(expr) = expr_a {
        collect_constants_and_shifts(expr, &mut raw, &mut shifts);
    }
    if let Some(expr) = expr_b {
        collect_constants_and_shifts(expr, &mut raw, &mut shifts);
    }

    for value in &mut raw {
        *value &= mask;
    }
    raw.sort_unstable();
    raw.dedup();
    raw.retain(|value| *value != 0 && *value != 1);

    shifts.sort_unstable();
    shifts.dedup();

    let mut derived = Vec::with_capacity(raw.len() * 6 + raw.len().saturating_mul(raw.len()));
    for &constant in &raw {
        derived.push(constant);
        derived.push(constant.wrapping_add(1) & mask);
        derived.push(constant.wrapping_sub(1) & mask);
        derived.push(!constant & mask);
        for &shift in &shifts {
            if shift < u64::from(bitwidth) {
                derived.push((constant >> shift) & mask);
            }
        }
    }

    if raw.len() <= 8 {
        for i in 0..raw.len() {
            for j in (i + 1)..raw.len() {
                derived.push((raw[i] ^ raw[j]) & mask);
                derived.push(raw[i].wrapping_add(raw[j]) & mask);
                derived.push(raw[i].wrapping_sub(raw[j]) & mask);
            }
        }
    }

    derived.sort_unstable();
    derived.dedup();
    derived.retain(|value| *value != 0 && *value != 1);
    if derived.len() > 128 {
        derived.truncate(128);
    }
    derived
}

fn collect_constants_and_shifts(
    expr: &Expr,
    constants: &mut Vec<u64>,
    shift_amounts: &mut Vec<u64>,
) {
    match &expr.kind {
        Kind::Constant(value) => constants.push(*value),
        Kind::Shr(amount) => shift_amounts.push(u64::from(*amount)),
        _ => {}
    }
    for child in &expr.children {
        collect_constants_and_shifts(child, constants, shift_amounts);
    }
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

/// Small curated set of "interesting" values: 0, 1, -1, -2, -3, -4,
/// 2^k-1 / 2^k / 2^k+1 for each bit position, plus 3/5/7 and the
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
    fn signature_check_reports_boolean_counterexample() {
        let sig = vec![0, 1, 1, 0];
        let simplified = Expr::or(Expr::variable(0), Expr::variable(1));
        let r = signature_check(&sig, &simplified, 2, 64);
        assert!(!r.passed);
        assert_eq!(r.failing_input, vec![1, 1]);
    }

    #[test]
    fn full_width_check_handles_var_map() {
        let original = Expr::add(Expr::variable(0), Expr::variable(2));
        let simplified = Expr::add(Expr::variable(0), Expr::variable(1));
        let r = full_width_check(&original, 3, &simplified, &[0, 2], 64, DEFAULT_NUM_SAMPLES);
        assert!(r.passed);
    }

    #[test]
    fn expression_derived_constant_probe_catches_mismatch() {
        let eval = Evaluator::from_closure(|vals| u64::from(vals[0] == 0x1234));
        let simplified = Expr::mul(
            Expr::constant(0),
            Expr::add(Expr::variable(0), Expr::constant(0x1234)),
        );
        let r = full_width_check_eval(&eval, 1, &simplified, 16, 0);
        assert!(!r.passed);
        assert_eq!(r.failing_input, vec![0x1234]);
    }

    #[test]
    fn eval_expr_matches_modular_semantics() {
        let expr = Expr::add(
            Expr::not(Expr::variable(0)),
            Expr::shr(Expr::constant(0xF0), 4),
        );
        assert_eq!(eval_expr(&expr, &[0x0F], 8), 0xFF);
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
