//! Auxiliary-variable elimination. A variable is "spurious" if toggling
//! it never changes any entry of the signature vector. Removing
//! spurious variables reduces the problem size passed to downstream
//!
//! Two entry points:
//! - [`eliminate_aux_vars`] — signature-only (Boolean-level). Cheap
//!   but can over-eliminate variables that look spurious on `{0, 1}`
//!   but are live at full width (e.g. `x*y` differs from `x&y` only
//!   outside the Boolean cube).
//! - [`eliminate_aux_vars_fw`] — Boolean elimination followed by a
//!   full-width probe via the caller's evaluator. Variables that
//!   toggle the output at any random sample are promoted back to

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;

use cobra_orchestrator::EliminationResult;

/// True if toggling `var_bit` never changes any paired entry of `sig`.
/// For every assignment `i` with bit `var_bit` cleared, compare with
/// `i | (1 << var_bit)`.
fn is_spurious(sig: &[u64], var_bit: u32, num_vars: u32) -> bool {
    let len = 1usize << num_vars;
    let stride = 1usize << var_bit;
    for i in 0..len {
        if i & stride != 0 {
            continue;
        }
        let j = i | stride;
        if sig[i] != sig[j] {
            return false;
        }
    }
    true
}

/// Bitmask of live variables (bit `v` set iff variable `v` is not
/// spurious).
fn detect_live_mask(sig: &[u64], num_vars: u32) -> u64 {
    let mut live: u64 = 0;
    for v in 0..num_vars {
        if !is_spurious(sig, v, num_vars) {
            live |= 1u64 << v;
        }
    }
    live
}

/// Compact a signature vector by dropping dimensions whose bit is
/// cleared in `live_mask`. Entries collapse to the indices where the
/// cleared bits are zero (they all share the same value).
fn compact_sig(sig: &[u64], live_mask: u64, num_vars: u32) -> Vec<u64> {
    // `count_ones()` gives the new arity; the new signature has length
    // `2^real_count`. For each assignment `i` in `0..2^num_vars`, keep
    // only those where every cleared bit in `live_mask` is zero (so we
    // don't double-count collapsed entries).
    let len = 1usize << num_vars;
    let dead_mask = !live_mask & ((1u64 << num_vars).wrapping_sub(1));
    let mut out = Vec::with_capacity(1usize << live_mask.count_ones());
    for i in 0..len {
        if (i as u64) & dead_mask != 0 {
            continue;
        }
        // Pack live bits of `i` down into a contiguous index.
        let mut packed: u64 = 0;
        let mut bit_out: u32 = 0;
        for v in 0..num_vars {
            if live_mask & (1u64 << v) != 0 {
                if (i as u64) & (1u64 << v) != 0 {
                    packed |= 1u64 << bit_out;
                }
                bit_out += 1;
            }
        }
        out.push(sig[packed_source_index(packed, live_mask, num_vars) as usize]);
    }
    out
}

/// Given a `packed` index over live bits only, expand it back to the
/// full index space using `live_mask`. Inverse of the bit-packing
/// used in [`compact_sig`].
fn packed_source_index(packed: u64, live_mask: u64, num_vars: u32) -> u64 {
    let mut src: u64 = 0;
    let mut bit_in: u32 = 0;
    for v in 0..num_vars {
        if live_mask & (1u64 << v) != 0 {
            if packed & (1u64 << bit_in) != 0 {
                src |= 1u64 << v;
            }
            bit_in += 1;
        }
    }
    src
}

/// Eliminate spurious variables from `sig`. Returns an
/// [`EliminationResult`] with the compacted signature and the
/// real/spurious variable name lists.
///
/// When `num_vars == 0` (constant input) the result contains the
/// original signature untouched and empty variable lists.
#[must_use]
pub fn eliminate_aux_vars(sig: &[u64], vars: &[String]) -> EliminationResult {
    let num_vars = vars.len() as u32;
    if num_vars == 0 {
        return EliminationResult {
            reduced_sig: sig.to_vec(),
            real_vars: Vec::new(),
            spurious_vars: Vec::new(),
        };
    }

    let live = detect_live_mask(sig, num_vars);
    if live == (1u64 << num_vars).wrapping_sub(1) {
        // All live — nothing to eliminate.
        return EliminationResult {
            reduced_sig: sig.to_vec(),
            real_vars: vars.to_vec(),
            spurious_vars: Vec::new(),
        };
    }

    // Partition variable names.
    let mut real_vars = Vec::new();
    let mut spurious_vars = Vec::new();
    for (v, name) in vars.iter().enumerate() {
        if live & (1u64 << v) != 0 {
            real_vars.push(name.clone());
        } else {
            spurious_vars.push(name.clone());
        }
    }

    let reduced_sig = extract_live_entries(sig, live, num_vars);
    EliminationResult {
        reduced_sig,
        real_vars,
        spurious_vars,
    }
}

/// Full-width variant of [`eliminate_aux_vars`]: runs the Boolean
/// elimination first, then re-checks each variable marked spurious
/// by sampling the evaluator at random full-width points. A variable
/// whose toggle changes the output at any probe is promoted back to
#[must_use]
pub fn eliminate_aux_vars_fw(
    sig: &[u64],
    vars: &[String],
    eval: &Evaluator,
    bitwidth: u32,
) -> EliminationResult {
    let mut result = eliminate_aux_vars(sig, vars);
    let num_vars = vars.len() as u32;
    if num_vars == 0 || result.spurious_vars.is_empty() {
        return result;
    }

    let mut var_idx: std::collections::HashMap<String, u32> =
        std::collections::HashMap::with_capacity(num_vars as usize);
    for (j, v) in vars.iter().enumerate() {
        var_idx.insert(v.clone(), j as u32);
    }

    let mut still_spurious: Vec<String> = Vec::new();
    for sv in &result.spurious_vars {
        let idx = *var_idx.get(sv).expect("spurious var is from vars list");
        if is_spurious_full_width(eval, idx, num_vars, bitwidth) {
            still_spurious.push(sv.clone());
        } else {
            result.real_vars.push(sv.clone());
        }
    }
    result.spurious_vars = still_spurious;

    // Re-sort real_vars / spurious_vars by original index.
    result
        .real_vars
        .sort_by_key(|s| *var_idx.get(s).expect("real var is from vars list"));
    result
        .spurious_vars
        .sort_by_key(|s| *var_idx.get(s).expect("spurious var is from vars list"));

    // Recompute live mask and reduced_sig in terms of the updated real_vars.
    let mut live: u64 = 0;
    for rv in &result.real_vars {
        live |= 1u64 << var_idx.get(rv).expect("live var is from vars list");
    }
    result.reduced_sig = extract_live_entries(sig, live, num_vars);
    result
}

fn is_spurious_full_width(eval: &Evaluator, var_index: u32, num_vars: u32, bitwidth: u32) -> bool {
    const NUM_SAMPLES: u32 = 8;
    let mask = bitmask(bitwidth);
    let mut state: u64 = (u64::from(var_index)).wrapping_mul(2_654_435_761)
        ^ (u64::from(num_vars)).wrapping_mul(40_503)
        ^ 0xDEAD_BEEFu64;
    let mut splitmix = || -> u64 {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let mut inputs = vec![0u64; num_vars as usize];
    for _ in 0..NUM_SAMPLES {
        for slot in &mut inputs {
            *slot = splitmix() & mask;
        }
        let v1 = eval.eval(&inputs) & mask;
        inputs[var_index as usize] = splitmix() & mask;
        let v2 = eval.eval(&inputs) & mask;
        if v1 != v2 {
            return false;
        }
    }
    true
}

/// Pull out `sig[i]` for every assignment `i` whose dead bits are zero.
/// Length = `2^popcount(live_mask)`.
fn extract_live_entries(sig: &[u64], live_mask: u64, num_vars: u32) -> Vec<u64> {
    let real_count = live_mask.count_ones();
    let out_len = 1usize << real_count;
    let mut out = Vec::with_capacity(out_len);
    for packed in 0..out_len {
        let src = packed_source_index(packed as u64, live_mask, num_vars) as usize;
        out.push(sig[src]);
    }
    let _ = compact_sig; // keep `compact_sig` available; currently unused.
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluate_boolean_signature;
    use cobra_core::expr::Expr;

    fn names(n: usize) -> Vec<String> {
        ('a'..).take(n).map(|c| c.to_string()).collect()
    }

    #[test]
    fn constant_signature_has_no_live_vars() {
        // "7" — zero variables, sig = [7].
        let sig = vec![7u64];
        let r = eliminate_aux_vars(&sig, &[]);
        assert!(r.real_vars.is_empty());
        assert!(r.spurious_vars.is_empty());
        assert_eq!(r.reduced_sig, sig);
    }

    #[test]
    fn all_vars_live_returns_everything() {
        // "x + y" — both variables matter.
        let expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let sig = evaluate_boolean_signature(&expr, 2, 64);
        let r = eliminate_aux_vars(&sig, &names(2));
        assert_eq!(r.real_vars, names(2));
        assert!(r.spurious_vars.is_empty());
        assert_eq!(r.reduced_sig, sig);
    }

    #[test]
    fn spurious_var_removed_and_sig_compacted() {
        // "x" in a 2-variable context — `y` never changes the output.
        // Sig = [0, 1, 0, 1]. `y` is spurious.
        let expr = Expr::variable(0);
        let sig = evaluate_boolean_signature(&expr, 2, 64);
        assert_eq!(sig, vec![0, 1, 0, 1]);
        let r = eliminate_aux_vars(&sig, &names(2));
        assert_eq!(r.real_vars, vec!["a".to_owned()]);
        assert_eq!(r.spurious_vars, vec!["b".to_owned()]);
        assert_eq!(r.reduced_sig, vec![0, 1]);
    }

    #[test]
    fn spurious_middle_variable_removed() {
        // Sig of "x + z" over three vars — `y` (var 1) is spurious.
        let expr = Expr::add(Expr::variable(0), Expr::variable(2));
        let sig = evaluate_boolean_signature(&expr, 3, 64);
        let r = eliminate_aux_vars(&sig, &names(3));
        assert_eq!(r.real_vars, vec!["a".to_owned(), "c".to_owned()]);
        assert_eq!(r.spurious_vars, vec!["b".to_owned()]);
        // Reduced sig is just the sig of "x + z" over two vars.
        let expected =
            evaluate_boolean_signature(&Expr::add(Expr::variable(0), Expr::variable(1)), 2, 64);
        assert_eq!(r.reduced_sig, expected);
    }
}
