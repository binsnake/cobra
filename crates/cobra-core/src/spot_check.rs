//! Signature and spot-check verification for simplified expressions.
//!
//! Full-width checks run the upstream probe schedule: adversarial values,
//! expression-derived constants, two-variable constant combinations, and a
//! deterministic random sample.

use crate::core::arith::bitmask;
use crate::core::compiled::{compile, eval as eval_compiled, try_compile, CompiledExpr};
use crate::core::evaluator::{Evaluator, Workspace};
use crate::core::expr::{Expr, Kind};
use crate::core::expr_utils::remap_var_indices;
use crate::core::signature_eval::{checked_signature_len, try_evaluate_boolean_signature};

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
    let Ok(len) = checked_signature_len(num_vars) else {
        return CheckResult::default();
    };
    let Ok(computed) = try_evaluate_boolean_signature(simplified, num_vars, bitwidth) else {
        return CheckResult::default();
    };
    let mask = bitmask(bitwidth);
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
    // Fail closed on a tree whose widths do not validate. `width_of` reports
    // an invalid width as 0 and `bitmask(0) == 0`, so such a program evaluates
    // to zero everywhere and would compare equal to a constant-0 candidate at
    // every probe point.
    let (Ok(original_prog), Ok(simplified_prog)) = (
        try_compile(original, bitwidth),
        try_compile(simplified, bitwidth),
    ) else {
        return CheckResult::default();
    };
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

    let expr_salt = expr_fingerprint(original) ^ expr_fingerprint(simplified).rotate_left(32);
    let failing = for_each_full_width_probe(
        original_num_vars,
        bitwidth,
        num_samples,
        &expr_constants,
        expr_salt,
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
    let Ok(simplified_prog) = try_compile(simplified, bitwidth) else {
        return CheckResult::default();
    };

    // Reject expressions wider than the caller's variable space — matches
    // the C++ arity guard.
    // `input_arity` is tracked for compiled and remapped-closure evaluators;
    // plain closures report 0 ("unknown"), which skips the guard.
    let original_arity = eval_original.input_arity();
    if original_arity > num_vars || simplified_prog.arity > num_vars {
        return CheckResult::default();
    }

    // Probe the constants of BOTH sides. The original is an `Evaluator`
    // rather than an `Expr`, so its constants come out of the compiled
    // program; omitting them let a candidate that differs from the original
    // only at an original-only trap constant pass this gate unchallenged.
    let mut raw = Vec::new();
    let mut shifts = Vec::new();
    eval_original.collect_constants_and_shifts(&mut raw, &mut shifts);
    collect_constants_and_shifts(simplified, &mut raw, &mut shifts);
    let expr_constants = derive_probes(raw, shifts, bitwidth);
    let mut simplified_stack: Vec<u64> = Vec::with_capacity(simplified_prog.stack_size);
    let mut original_workspace = Workspace::default();

    // Bind the seed to the ORIGINAL (via its compiled fingerprint, which
    // embeds every constant) as well as the candidate. The original carries
    // any adversarial trap constants, so they feed back into the seed and a
    // fixed-seed evasion cannot be constructed.
    let expr_salt =
        eval_original.structural_fingerprint() ^ expr_fingerprint(simplified).rotate_left(32);
    let failing = for_each_full_width_probe(
        num_vars,
        bitwidth,
        num_samples,
        &expr_constants,
        expr_salt,
        |inputs| {
            probe_point(
                eval_original,
                &simplified_prog,
                inputs,
                mask,
                &mut original_workspace,
                &mut simplified_stack,
            )
            .is_none()
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

/// Evaluate an expression at the provided variable values.
///
/// Thin wrapper over the compiled evaluator, which is the reference semantics.
/// This previously threaded the run-global `bitwidth` into every same-width
/// operator while its cast arms used node-local widths — two width models in
/// one function, disagreeing on any tree containing a cast.
///
/// Returns 0 for a tree whose widths do not validate; use
/// [`crate::core::compiled::try_compile`] to detect that case.
#[must_use]
pub fn eval_expr(expr: &Expr, var_values: &[u64], bitwidth: u32) -> u64 {
    let prog = compile(expr, bitwidth);
    let mut stack = Vec::with_capacity(prog.stack_size);
    eval_compiled(&prog, var_values, &mut stack)
}

fn for_each_full_width_probe(
    num_vars: u32,
    bitwidth: u32,
    num_samples: u32,
    expr_constants: &[u64],
    expr_salt: u64,
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

    let mut rng_state = seed_for(num_vars, bitwidth, num_samples, expr_salt);
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
    let mut raw = Vec::new();
    let mut shifts = Vec::new();
    if let Some(expr) = expr_a {
        collect_constants_and_shifts(expr, &mut raw, &mut shifts);
    }
    if let Some(expr) = expr_b {
        collect_constants_and_shifts(expr, &mut raw, &mut shifts);
    }
    derive_probes(raw, shifts, bitwidth)
}

/// Expand collected constants and shift amounts into the probe set.
fn derive_probes(mut raw: Vec<u64>, mut shifts: Vec<u64>, bitwidth: u32) -> Vec<u64> {
    let mask = bitmask(bitwidth);
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
                // Products close a real evasion: a trap constant is often
                // written as a product of two literals, which compiles to two
                // separate `Constant` instructions. Without this, no derived
                // probe ever lands on the value the trap actually fires at.
                derived.push(raw[i].wrapping_mul(raw[j]) & mask);
            }
            derived.push(raw[i].wrapping_mul(raw[i]) & mask);
        }
    }

    derived.sort_unstable();
    derived.dedup();
    derived.retain(|value| *value != 0 && *value != 1);
    clamp_probe_budget(&mut derived);
    derived
}

/// Number of derived probe points evaluated per check.
const MAX_DERIVED_PROBES: usize = 128;

/// Reduce the probe set to [`MAX_DERIVED_PROBES`] while keeping both ends of
/// the range.
///
/// The set is sorted ascending, so a plain `truncate` keeps only the
/// numerically smallest values and deterministically deletes every
/// high-magnitude probe — at bitwidth 64 that is every `!c` for `c < 2^63`,
/// plus any large literal. Splitting the budget between the low and high ends
/// keeps complements and large constants reachable.
fn clamp_probe_budget(derived: &mut Vec<u64>) {
    if derived.len() <= MAX_DERIVED_PROBES {
        return;
    }
    let high = MAX_DERIVED_PROBES / 2;
    let low = MAX_DERIVED_PROBES - high;
    let tail: Vec<u64> = derived[derived.len() - high..].to_vec();
    derived.truncate(low);
    derived.extend_from_slice(&tail);
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
    if compile(reduced_expr, bitwidth).arity > real_vars.len() as u32 {
        return CheckResult::default();
    }
    if real_vars == all_vars {
        return full_width_check_eval(eval, all_count, reduced_expr, bitwidth, DEFAULT_NUM_SAMPLES);
    }
    // When `real_vars` lives in a namespace other than `all_vars`
    // (residual / lifted-outer candidates), we can't remap. Report
    // the check as failed so the caller routes this candidate
    // through the group resolver rather than crashing.
    let Some(idx_map) = crate::core::expr_rewrite::try_build_var_support(all_vars, real_vars)
    else {
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

/// Deterministic structural fingerprint of an expression tree, folding in
/// every kind discriminant, variable index, and constant value. Used to salt
/// the probe seed (see [`seed_for`]).
fn expr_fingerprint(expr: &Expr) -> u64 {
    fn fold(expr: &Expr, acc: &mut u64) {
        let step = |tag: u64, payload: u64, acc: &mut u64| {
            let mut s = acc.wrapping_add(tag).wrapping_add(0x9E37_79B9_7F4A_7C15);
            *acc = splitmix64(&mut s).wrapping_add(payload);
        };
        match &expr.kind {
            Kind::Constant(v) => step(1, *v, acc),
            Kind::Variable(i) => step(2, u64::from(*i), acc),
            Kind::Add => step(3, 0, acc),
            Kind::Mul => step(4, 0, acc),
            Kind::And => step(5, 0, acc),
            Kind::Or => step(6, 0, acc),
            Kind::Xor => step(7, 0, acc),
            Kind::Not => step(8, 0, acc),
            Kind::Neg => step(9, 0, acc),
            Kind::Shr(k) => step(10, u64::from(*k), acc),
            Kind::ZExt(w) => step(11, u64::from(*w), acc),
            Kind::SExt(w) => step(12, u64::from(*w), acc),
            Kind::Trunc(w) => step(13, u64::from(*w), acc),
            Kind::Concat => step(14, 0, acc),
        }
        for child in &expr.children {
            fold(child, acc);
        }
    }
    let mut acc = 0x2545_F491_4F6C_DD1Du64;
    fold(expr, &mut acc);
    acc
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn seed_for(num_vars: u32, bitwidth: u32, num_samples: u32, expr_salt: u64) -> u64 {
    // Run each parameter through splitmix64 before combining so distinct
    // (num_vars, bitwidth, num_samples) triples get well-separated seeds;
    // plain multiply-xor mixing let nearby configurations collide.
    //
    // `expr_salt` binds the seed to a structural fingerprint of the
    // expression(s) under test (including every embedded constant). This keeps
    // the schedule fully deterministic for reproducibility, while preventing an
    // attacker from precomputing the random probe points: a difference term
    // engineered to vanish on the points would have to embed constants that, in
    // turn, change `expr_salt` and thus the points — a fixpoint that does not
    // exist in practice. See the verifier-evasion analysis in
    // `tools/adversarial/ATTACKS.md`.
    let mut state = u64::from(num_vars);
    let vars_mix = splitmix64(&mut state);
    state ^= u64::from(bitwidth) << 8;
    let width_mix = splitmix64(&mut state);
    state ^= u64::from(num_samples) << 16;
    let samples_mix = splitmix64(&mut state);
    state ^= expr_salt;
    let expression_mix = splitmix64(&mut state);
    vars_mix
        ^ width_mix.rotate_left(21)
        ^ samples_mix.rotate_left(42)
        ^ expression_mix.rotate_left(11)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::width::validate_widths;

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
    fn original_space_check_remaps_equal_length_permuted_names() {
        let original = Expr::variable(0);
        let eval = Evaluator::from_expr(&original, 64);
        let result = verify_in_original_space(
            &eval,
            &["a".to_owned(), "b".to_owned()],
            &["b".to_owned(), "a".to_owned()],
            &Expr::variable(0),
            64,
        );
        assert!(
            !result.passed,
            "b must not be checked as original variable a"
        );
    }

    #[test]
    fn original_space_check_rejects_nonconstant_empty_namespace() {
        let original = Expr::variable(0);
        let eval = Evaluator::from_expr(&original, 64);
        let result =
            verify_in_original_space(&eval, &["a".to_owned()], &[], &Expr::variable(0), 64);
        assert!(!result.passed);
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
    fn original_only_constant_probe_catches_trap_candidate() {
        // `((x ^ 0x1234) | -(x ^ 0x1234)) >> 63` is 1 everywhere except at
        // x == 0x1234, where it is 0. The trap constant lives only in the
        // ORIGINAL, so a probe set derived from the candidate alone never
        // reaches it and the candidate `1` slips through the gate.
        let trap = Expr::xor(Expr::variable(0), Expr::constant(0x1234));
        let original = Expr::shr(Expr::or(trap.clone(), Expr::neg(trap)), 63);
        let eval = Evaluator::from_expr(&original, 64);
        let candidate = Expr::constant(1);

        let r = full_width_check_eval(&eval, 1, &candidate, 64, 256);
        assert!(!r.passed, "trap-constant candidate must be rejected");
        assert_eq!(r.failing_input, vec![0x1234]);
    }

    #[test]
    fn product_derived_probe_catches_trap_constant() {
        // The trap fires only at x == 0x12345 * 0x10001. Both factors appear
        // as separate `Constant` instructions in the compiled program, so a
        // probe set without products never lands on the differing point.
        let target = Expr::mul(Expr::constant(0x1_2345), Expr::constant(0x1_0001));
        let delta = Expr::xor(Expr::variable(0), target);
        let nonzero = Expr::or(delta.clone_tree(), Expr::neg(delta));
        let original = Expr::shr(Expr::not(nonzero), 63);
        let eval = Evaluator::from_expr(&original, 64);

        // `original` is 1 exactly at the trap point and 0 everywhere else, so
        // the constant-0 candidate differs there and nowhere else.
        let r = full_width_check_eval(&eval, 1, &Expr::constant(0), 64, 256);
        assert!(!r.passed, "trap point must be probed");
        assert_eq!(r.failing_input, vec![0x1_2345u64.wrapping_mul(0x1_0001)]);
    }

    #[test]
    fn probe_budget_keeps_both_ends_of_the_range() {
        let mut probes: Vec<u64> = (0..400u64).map(|i| i * 3).collect();
        let lowest = probes[0];
        let highest = *probes.last().expect("non-empty");
        clamp_probe_budget(&mut probes);

        assert_eq!(probes.len(), MAX_DERIVED_PROBES);
        assert_eq!(probes[0], lowest, "low end must survive");
        assert_eq!(
            *probes.last().expect("non-empty"),
            highest,
            "high end must survive truncation"
        );
    }

    #[test]
    fn invalid_width_tree_fails_closed_instead_of_evaluating_to_zero() {
        // At bitwidth 64 a Concat over bare 64-bit variables cannot be
        // represented, so `width_of` reports 0 and the compiled program masks
        // everything to zero. Left unchecked it compares equal to constant 0
        // at every probe point.
        let invalid = Expr::add(
            Expr::mul(
                Expr::concat(Expr::variable(0), Expr::variable(1)),
                Expr::variable(2),
            ),
            Expr::variable(2),
        );
        assert!(crate::core::compiled::try_compile(&invalid, 64).is_err());
        assert!(Evaluator::try_from_expr(&invalid, 64).is_err());

        let r = full_width_check(&invalid, 3, &Expr::constant(0), &[], 64, 64);
        assert!(!r.passed, "an unrepresentable tree must not verify as zero");
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
    fn eval_expr_agrees_with_compiled_over_mixed_width_corpus() {
        // The three tree-walking evaluators used to thread the run-global
        // bitwidth into same-width operators while their cast arms used
        // node-local widths. Any tree mixing a cast with arithmetic exposed
        // the disagreement, so pin the two models together.
        use crate::core::compiled::{compile, eval as eval_compiled};

        let leaves = [
            Expr::variable(0),
            Expr::variable(1),
            Expr::constant(0xFF),
            Expr::trunc(Expr::variable(0), 8),
            Expr::zext(Expr::trunc(Expr::variable(0), 8), 32),
            Expr::sext(Expr::trunc(Expr::variable(1), 8), 32),
        ];

        let mut checked = 0u32;
        for (i, a) in leaves.iter().enumerate() {
            for (j, b) in leaves.iter().enumerate() {
                // Same-width binaries need both sides at one width, so pair a
                // leaf only with itself-width partners plus the unary arms.
                let candidates = vec![
                    Expr::not(a.clone_tree()),
                    Expr::neg(a.clone_tree()),
                    Expr::shr(a.clone_tree(), 3),
                ];
                let mut trees = candidates;
                if i == j {
                    trees.push(Expr::add(a.clone_tree(), b.clone_tree()));
                    trees.push(Expr::mul(a.clone_tree(), b.clone_tree()));
                    trees.push(Expr::xor(a.clone_tree(), b.clone_tree()));
                    trees.push(Expr::and(a.clone_tree(), b.clone_tree()));
                }
                for tree in trees {
                    if validate_widths(&tree, &[], 64).is_err() {
                        continue;
                    }
                    for seed in 0u64..8 {
                        let point = [
                            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15),
                            seed.wrapping_mul(0xD6E8_FEB8_6659_FD93),
                        ];
                        let prog = compile(&tree, 64);
                        let mut stack = Vec::with_capacity(prog.stack_size);
                        assert_eq!(
                            eval_expr(&tree, &point, 64),
                            eval_compiled(&prog, &point, &mut stack),
                            "walker and compiled evaluator disagree on {tree:?} at {point:?}"
                        );
                        checked += 1;
                    }
                }
            }
        }
        assert!(checked > 200, "corpus should be non-trivial, got {checked}");
    }

    #[test]
    fn eval_expr_casts_and_concat() {
        // zext(a, 16) with an 8-bit var a=0xAB -> 0x00AB.
        let e = Expr::zext(Expr::variable(0), 16);
        assert_eq!(eval_expr(&e, &[0xAB], 8), 0x00AB);

        // sext(a, 16) with a=0xFF (8-bit -1) -> 0xFFFF.
        let e = Expr::sext(Expr::variable(0), 16);
        assert_eq!(eval_expr(&e, &[0xFF], 8), 0xFFFF);

        // trunc(a, 8) with a 16-bit var 0xABCD -> 0xCD.
        let e = Expr::trunc(Expr::variable(0), 8);
        assert_eq!(eval_expr(&e, &[0xABCD], 16), 0xCD);

        // concat(a:u8, b:u8): high 0x12, low 0x34 -> 0x1234.
        let e = Expr::concat(Expr::variable(0), Expr::variable(1));
        assert_eq!(eval_expr(&e, &[0x12, 0x34], 8), 0x1234);

        // Cross-check the concat == zext-arith identity at one point.
        let lhs = Expr::concat(Expr::variable(0), Expr::variable(1));
        let rhs = Expr::add(
            Expr::mul(Expr::zext(Expr::variable(0), 16), Expr::constant(256)),
            Expr::zext(Expr::variable(1), 16),
        );
        assert_eq!(
            eval_expr(&lhs, &[0x80, 0x01], 8),
            eval_expr(&rhs, &[0x80, 0x01], 16)
        );
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
