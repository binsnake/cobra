//! Builds a minimum-cost `Expr` tree from ANF coefficients.
//!
//! `AnfForm` is the mid-level representation: a list of monomial bitmasks
//! (each bit is a variable) plus an optional constant term. Four
//! rewrite rules compete on tree cost:
//!
//! 1. Full OR recognizer — when the monomial set equals every non-empty
//!    subset of some variable union, the expression collapses to a
//!    single `OR`-chain.
//! 2. Partial OR recognition — a subset of monomials forms an OR-family
//!    and can be peeled off as an OR-chain XOR'd with the remainder.
//! 3. Common-cube factoring — a shared variable mask is factored out of
//!    a cover of monomials.
//! 4. Two-monomial absorption — `M ^ (M & N)` rewrites to `M & ~N`.
//!
//! The winner is whichever rule produces the lowest [`anf_expr_cost`].

use std::collections::{HashMap, HashSet};

use cobra_core::expr::{Expr, Kind};

use crate::packed_anf::PackedAnf;

/// Mid-level ANF representation consumed by [`cleanup_anf`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AnfForm {
    pub constant_bit: u8,
    pub monomials: Vec<u32>, // nonzero masks, sorted by (popcount, mask)
    pub num_vars: u32,
}

impl AnfForm {
    /// Extract monomials from a [`PackedAnf`] coefficient bitvector,
    /// separating the constant term (index 0).
    #[must_use]
    pub fn from_anf_coeffs(anf: &PackedAnf, num_vars: u32) -> Self {
        let constant_bit = u8::from(!anf.is_empty() && anf.get(0) != 0);
        let mut monomials = Vec::new();
        for w in 0..anf.word_count() {
            let mut bits = anf.word(w);
            if w == 0 {
                bits &= !1u64;
            }
            while bits != 0 {
                let bit = bits.trailing_zeros();
                let idx = (w as u32) * 64 + bit;
                monomials.push(idx);
                bits &= bits - 1;
            }
        }
        monomials.sort_by(|a, b| monomial_less(*a, *b));
        Self {
            constant_bit,
            monomials,
            num_vars,
        }
    }
}

#[inline]
fn monomial_less(a: u32, b: u32) -> std::cmp::Ordering {
    let da = a.count_ones();
    let db = b.count_ones();
    da.cmp(&db).then_with(|| a.cmp(&b))
}

/// Node-count cost of a monomial AND-chain built by [`build_monomial`].
#[inline]
fn monomial_expr_cost(mask: u32) -> u32 {
    let pc = mask.count_ones();
    if pc == 0 {
        1
    } else {
        2 * pc - 1
    }
}

/// Node-count cost of a raw ANF XOR-tree without materialising the Expr.
fn raw_anf_cost(monomials: &[u32], constant_bit: u8) -> u32 {
    let n = monomials.len() as u32 + u32::from(constant_bit);
    if n == 0 {
        return 1;
    }
    let mut leaf_cost: u32 = u32::from(constant_bit);
    for &m in monomials {
        leaf_cost += monomial_expr_cost(m);
    }
    leaf_cost + n.saturating_sub(1)
}

/// Cost of an OR-chain over `k` variables with the depth discount
/// applied (same discount logic as [`anf_expr_cost`]).
fn or_chain_cost(var_mask: u32) -> u32 {
    let k = var_mask.count_ones();
    match k {
        0 | 1 => 1,
        2 => 3,
        _ => k + 1,
    }
}

fn build_monomial(mask: u32) -> Box<Expr> {
    let vars: Vec<u32> = (0..32).filter(|i| (mask >> i) & 1 == 1).collect();
    assert!(!vars.is_empty(), "empty monomial has no Expr");
    let mut result = Expr::variable(vars[0]);
    for &v in &vars[1..] {
        result = Expr::and(result, Expr::variable(v));
    }
    result
}

#[allow(clippy::vec_box)] // `Box<Expr>` matches the factory shape; unboxing would force re-heap-allocs
fn xor_tree(terms: Vec<Box<Expr>>) -> Box<Expr> {
    // Balanced binary fold using an Option-slot buffer so we can move
    // ownership out without cloning the subtrees.
    fn recurse(slice: &mut [Option<Box<Expr>>]) -> Box<Expr> {
        if slice.len() == 1 {
            return slice[0].take().expect("xor_tree slot already consumed");
        }
        let mid = slice.len() / 2;
        let (lo, hi) = slice.split_at_mut(mid);
        Expr::xor(recurse(lo), recurse(hi))
    }
    let mut slots: Vec<Option<Box<Expr>>> = terms.into_iter().map(Some).collect();
    recurse(&mut slots)
}

fn count_or_chain_depth(expr: &Expr) -> u32 {
    if !matches!(expr.kind, Kind::Or) {
        return 0;
    }
    1 + count_or_chain_depth(&expr.children[0])
}

/// `ExprCost` in `AnfCleanup.cpp`.
#[must_use]
pub fn anf_expr_cost(expr: &Expr) -> u32 {
    match &expr.kind {
        Kind::Constant(_) | Kind::Variable(_) => 1,
        Kind::Not | Kind::Neg => 1 + anf_expr_cost(&expr.children[0]),
        Kind::Shr(_) | Kind::Add | Kind::Mul | Kind::And | Kind::Xor => {
            1 + anf_expr_cost(&expr.children[0]) + anf_expr_cost(&expr.children[1])
        }
        Kind::Or => {
            let base = 1 + anf_expr_cost(&expr.children[0]) + anf_expr_cost(&expr.children[1]);
            let depth = count_or_chain_depth(expr);
            if depth >= 2 {
                base - 1
            } else {
                base
            }
        }
    }
}

/// Emit a raw XOR-of-monomials tree without any cleanup.
#[must_use]
pub fn emit_raw_anf(form: &AnfForm) -> Box<Expr> {
    let mut terms: Vec<Box<Expr>> = Vec::new();
    if form.constant_bit != 0 {
        terms.push(Expr::constant(1));
    }
    for &m in &form.monomials {
        terms.push(build_monomial(m));
    }
    match terms.len() {
        0 => Expr::constant(0),
        1 => terms.into_iter().next().unwrap(),
        _ => xor_tree(terms),
    }
}

fn build_or_chain(var_mask: u32) -> Box<Expr> {
    let vars: Vec<u32> = (0..32).filter(|i| (var_mask >> i) & 1 == 1).collect();
    assert!(!vars.is_empty(), "empty OR-chain");
    let mut result = Expr::variable(vars[0]);
    for &v in &vars[1..] {
        result = Expr::or(result, Expr::variable(v));
    }
    result
}

fn detect_or_family(monomials: &[u32]) -> Option<u32> {
    if monomials.is_empty() {
        return None;
    }
    let mut var_union: u32 = 0;
    for &m in monomials {
        if m.is_power_of_two() {
            var_union |= m;
        }
    }
    if var_union == 0 {
        return None;
    }
    let nv = var_union.count_ones();
    let expected = (1usize << nv) - 1;
    if monomials.len() != expected {
        return None;
    }
    let bits: Vec<u32> = (0..32)
        .filter(|i| (var_union >> i) & 1 == 1)
        .map(|i| 1u32 << i)
        .collect();
    let mono_set: HashSet<u32> = monomials.iter().copied().collect();
    let total = 1u32 << bits.len();
    for s in 1..total {
        let mut mask = 0u32;
        for (b, &bit) in bits.iter().enumerate() {
            if (s >> b) & 1 == 1 {
                mask |= bit;
            }
        }
        if !mono_set.contains(&mask) {
            return None;
        }
    }
    Some(var_union)
}

#[derive(Clone, Debug)]
struct FactorCandidate {
    factor_mask: u32,
    covered_indices: Vec<u32>,
}

type AnfCache = HashMap<(Vec<u32>, u8), Box<Expr>>;

fn find_best_factor(form: &AnfForm, cache: &mut AnfCache) -> Option<FactorCandidate> {
    if form.monomials.len() < 2 {
        return None;
    }
    let mut candidates: Vec<u32> = Vec::new();
    let mut all_vars: u32 = 0;
    for &m in &form.monomials {
        all_vars |= m;
    }
    // Single-variable candidates.
    for i in 0..32 {
        if (all_vars >> i) & 1 == 1 {
            candidates.push(1u32 << i);
        }
    }
    // Pairwise-intersection candidates with popcount ≥ 2.
    for i in 0..form.monomials.len() {
        for j in i + 1..form.monomials.len() {
            let common = form.monomials[i] & form.monomials[j];
            if common != 0 && common.count_ones() >= 2 {
                candidates.push(common);
            }
        }
    }
    candidates.sort_unstable();
    candidates.dedup();

    let mut best: Option<FactorCandidate> = None;
    let mut best_saving: u32 = 0;
    for &cand in &candidates {
        let covered: Vec<u32> = form
            .monomials
            .iter()
            .enumerate()
            .filter_map(|(i, &m)| ((m & cand) == cand).then_some(i as u32))
            .collect();
        if covered.len() < 2 {
            continue;
        }

        let mut inner = AnfForm {
            constant_bit: 0,
            monomials: Vec::new(),
            num_vars: form.num_vars,
        };
        for &idx in &covered {
            let stripped = form.monomials[idx as usize] & !cand;
            if stripped == 0 {
                inner.constant_bit = 1;
            } else {
                inner.monomials.push(stripped);
            }
        }
        inner.monomials.sort_by(|a, b| monomial_less(*a, *b));

        let covered_monos: Vec<u32> = covered
            .iter()
            .map(|&idx| form.monomials[idx as usize])
            .collect();
        let raw_cost = raw_anf_cost(&covered_monos, 0);

        let factor_cost = monomial_expr_cost(cand);
        if 1 + factor_cost >= raw_cost {
            continue;
        }

        let inner_expr = cleanup_anf_memo(&inner, cache);
        let factored_cost = 1 + factor_cost + anf_expr_cost(&inner_expr);
        if factored_cost < raw_cost {
            let saving = raw_cost - factored_cost;
            if saving > best_saving {
                best_saving = saving;
                best = Some(FactorCandidate {
                    factor_mask: cand,
                    covered_indices: covered,
                });
            }
        }
    }
    best
}

#[derive(Clone, Debug)]
struct PartialOrCandidate {
    var_mask: u32,
    family_masks: Vec<u32>,
}

fn find_partial_or(monomials: &[u32]) -> Option<PartialOrCandidate> {
    if monomials.len() < 3 {
        return None;
    }
    let mono_set: HashSet<u32> = monomials.iter().copied().collect();
    let mut all_vars: u32 = 0;
    for &m in monomials {
        all_vars |= m;
    }
    let var_bits: Vec<u32> = (0..32)
        .filter(|i| (all_vars >> i) & 1 == 1)
        .map(|i| 1u32 << i)
        .collect();
    let nv = var_bits.len();
    if nv < 2 {
        return None;
    }

    // A var_mask yields a valid partial-OR family iff every non-empty submask
    // of var_mask is present in `mono_set`. In particular, var_mask itself is
    // a non-empty submask of itself, so var_mask MUST be a monomial. This
    // reduces candidates from O(2^nv) to O(|monomials|).
    //
    // Map each var_mask to its original `s`-index (bits packed according to
    // `var_bits` position) so we iterate candidates in the exact same order
    // as the original enumeration. This preserves first-wins tie-breaking on
    // equal savings.
    let mut pos_in_var_bits = [0u8; 32];
    for (b, &bit) in var_bits.iter().enumerate() {
        pos_in_var_bits[bit.trailing_zeros() as usize] = b as u8;
    }
    let pack_s = |var_mask: u32| -> u32 {
        let mut s = 0u32;
        let mut m = var_mask;
        while m != 0 {
            let bit_idx = m.trailing_zeros();
            s |= 1u32 << pos_in_var_bits[bit_idx as usize];
            m &= m - 1;
        }
        s
    };

    let mut candidates: Vec<(u32, u32)> = monomials
        .iter()
        .copied()
        .filter(|m| m.count_ones() >= 2)
        .map(|m| (pack_s(m), m))
        .collect();
    candidates.sort_unstable_by_key(|&(s, _)| s);

    let mut best: Option<PartialOrCandidate> = None;
    let mut best_saving: u32 = 0;
    for &(_s, var_mask) in &candidates {
        let subset_size = var_mask.count_ones();
        let family_size = (1usize << subset_size) - 1;
        // Full-family case is handled by Rule 1.
        if family_size >= monomials.len() {
            continue;
        }

        // Enumerate all non-empty submasks of var_mask; all must be monomials.
        let mut family_masks: Vec<u32> = Vec::with_capacity(family_size);
        let mut sub = var_mask;
        let mut ok = true;
        loop {
            if !mono_set.contains(&sub) {
                ok = false;
                break;
            }
            family_masks.push(sub);
            if sub == 0 {
                break;
            }
            sub = (sub - 1) & var_mask;
            if sub == 0 {
                break;
            }
        }
        if !ok {
            continue;
        }

        let oc = or_chain_cost(var_mask);
        let rc = raw_anf_cost(&family_masks, 0);
        if oc < rc {
            let saving = rc - oc;
            if saving > best_saving {
                best_saving = saving;
                best = Some(PartialOrCandidate {
                    var_mask,
                    family_masks,
                });
            }
        }
    }
    best
}

#[derive(Clone, Debug)]
struct AbsorptionCandidate {
    m_idx: usize,
    _mn_idx: usize,
    n_mask: u32,
}

fn find_absorption(form: &AnfForm) -> Option<AbsorptionCandidate> {
    if form.monomials.len() != 2 {
        return None;
    }
    let a = form.monomials[0];
    let b = form.monomials[1];
    let raw_cost = raw_anf_cost(&form.monomials, form.constant_bit);

    let try_side =
        |small: u32, big: u32, m_idx: usize, mn_idx: usize| -> Option<AbsorptionCandidate> {
            if (small & big) == small && small != big {
                let n = big & !small;
                let absorption_cost = 2 + monomial_expr_cost(small) + monomial_expr_cost(n);
                if absorption_cost < raw_cost {
                    return Some(AbsorptionCandidate {
                        m_idx,
                        _mn_idx: mn_idx,
                        n_mask: n,
                    });
                }
            }
            None
        };

    try_side(a, b, 0, 1).or_else(|| try_side(b, a, 1, 0))
}

/// Build the optimal `Expr` tree for an ANF monomial set.
#[must_use]
pub fn cleanup_anf(form: &AnfForm) -> Box<Expr> {
    let mut cache = AnfCache::new();
    cleanup_anf_memo(form, &mut cache)
}

#[allow(clippy::too_many_lines)]
fn cleanup_anf_memo(form: &AnfForm, cache: &mut AnfCache) -> Box<Expr> {
    if form.monomials.is_empty() {
        return Expr::constant(u64::from(form.constant_bit));
    }

    // Memoization: key on (sorted monomials, constant_bit). The monomials are
    // kept sorted by every AnfForm constructor / mutation in this module, so
    // the raw Vec<u32> is already canonical.
    let key = (form.monomials.clone(), form.constant_bit);
    if let Some(cached) = cache.get(&key) {
        return cached.clone();
    }

    // Rule 1: full OR family (exact match across all monomials).
    if let Some(var_mask) = detect_or_family(&form.monomials) {
        let or_expr = build_or_chain(var_mask);
        let result = if form.constant_bit != 0 {
            Expr::xor(Expr::constant(1), or_expr)
        } else {
            or_expr
        };
        cache.insert(key, result.clone());
        return result;
    }

    let raw = emit_raw_anf(form);
    let raw_cost = anf_expr_cost(&raw);
    let mut best: Option<Box<Expr>> = None;
    let mut best_cost = raw_cost;

    // Rule 2: partial OR.
    if let Some(partial) = find_partial_or(&form.monomials) {
        let or_expr = build_or_chain(partial.var_mask);
        let family_set: HashSet<u32> = partial.family_masks.iter().copied().collect();
        let mut remainder = AnfForm {
            constant_bit: form.constant_bit,
            monomials: form
                .monomials
                .iter()
                .copied()
                .filter(|m| !family_set.contains(m))
                .collect(),
            num_vars: form.num_vars,
        };
        remainder.monomials.sort_by(|a, b| monomial_less(*a, *b));

        let result = if remainder.monomials.is_empty() && remainder.constant_bit == 0 {
            or_expr
        } else {
            let rem_expr = cleanup_anf_memo(&remainder, cache);
            Expr::xor(or_expr, rem_expr)
        };
        let cost = anf_expr_cost(&result);
        if cost < best_cost {
            best_cost = cost;
            best = Some(result);
        }
    }

    // Rule 3: common-cube factor.
    if let Some(factor) = find_best_factor(form, cache) {
        let covered_set: HashSet<u32> = factor.covered_indices.iter().copied().collect();
        let mut inner = AnfForm {
            constant_bit: 0,
            monomials: Vec::new(),
            num_vars: form.num_vars,
        };
        for &idx in &factor.covered_indices {
            let stripped = form.monomials[idx as usize] & !factor.factor_mask;
            if stripped == 0 {
                inner.constant_bit = 1;
            } else {
                inner.monomials.push(stripped);
            }
        }
        inner.monomials.sort_by(|a, b| monomial_less(*a, *b));
        let inner_expr = cleanup_anf_memo(&inner, cache);
        let factor_expr = build_monomial(factor.factor_mask);
        let factored = Expr::and(factor_expr, inner_expr);

        let mut remainder = AnfForm {
            constant_bit: form.constant_bit,
            monomials: form
                .monomials
                .iter()
                .enumerate()
                .filter_map(|(i, &m)| (!covered_set.contains(&(i as u32))).then_some(m))
                .collect(),
            num_vars: form.num_vars,
        };
        remainder.monomials.sort_by(|a, b| monomial_less(*a, *b));

        let result = if remainder.monomials.is_empty() && remainder.constant_bit == 0 {
            factored
        } else {
            let rem_expr = cleanup_anf_memo(&remainder, cache);
            Expr::xor(factored, rem_expr)
        };
        let cost = anf_expr_cost(&result);
        if cost < best_cost {
            best_cost = cost;
            best = Some(result);
        }
    }

    // Rule 4: two-monomial absorption.
    if let Some(absorb) = find_absorption(form) {
        let m_expr = build_monomial(form.monomials[absorb.m_idx]);
        let not_n = Expr::not(build_monomial(absorb.n_mask));
        let mut result = Expr::and(m_expr, not_n);
        if form.constant_bit != 0 {
            result = Expr::xor(Expr::constant(1), result);
        }
        let cost = anf_expr_cost(&result);
        if cost < best_cost {
            best = Some(result);
        }
    }

    let result = best.unwrap_or(raw);
    cache.insert(key, result.clone());
    result
}

/// Convenience wrapper: build the ANF-optimised Expr from a
/// [`PackedAnf`] coefficient vector.
#[must_use]
pub fn build_anf_expr(anf: &PackedAnf, num_vars: u32) -> Box<Expr> {
    let form = AnfForm::from_anf_coeffs(anf, num_vars);
    cleanup_anf(&form)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::evaluate_boolean_signature;

    fn form_from_sig(sig: &[u64], num_vars: u32) -> AnfForm {
        let anf = crate::anf_transform::compute_anf(sig, num_vars);
        AnfForm::from_anf_coeffs(&anf, num_vars)
    }

    #[test]
    fn empty_anf_is_constant_zero() {
        let form = AnfForm {
            constant_bit: 0,
            monomials: Vec::new(),
            num_vars: 2,
        };
        let e = cleanup_anf(&form);
        assert!(matches!(e.kind, Kind::Constant(0)));
    }

    #[test]
    fn constant_only_anf_is_constant_one() {
        let form = AnfForm {
            constant_bit: 1,
            monomials: Vec::new(),
            num_vars: 2,
        };
        let e = cleanup_anf(&form);
        assert!(matches!(e.kind, Kind::Constant(1)));
    }

    #[test]
    fn anf_xor_of_x_and_y() {
        // f = x ^ y — two linear monomials, no OR/factor/absorption rule
        // applies. Should emit the raw XOR tree.
        let form = form_from_sig(&[0, 1, 1, 0], 2);
        let e = cleanup_anf(&form);
        // Ensure the signature round-trips.
        assert_eq!(evaluate_boolean_signature(&e, 2, 1), vec![0, 1, 1, 0]);
    }

    #[test]
    fn anf_full_or_family_collapses_to_or_chain() {
        // f = x | y — ANF monomials are {x, y, xy}. Rule 1 fires.
        let form = form_from_sig(&[0, 1, 1, 1], 2);
        let e = cleanup_anf(&form);
        assert!(matches!(e.kind, Kind::Or));
        assert_eq!(evaluate_boolean_signature(&e, 2, 1), vec![0, 1, 1, 1]);
    }

    #[test]
    fn anf_absorption_m_xor_mn_is_and_with_not_n() {
        // f = x ^ (x & y) = x & ~y — Rule 4 (absorption) fires.
        let sig = vec![0, 1, 0, 0]; // bit 1 = x, bit 3 = xy → ANF {x, xy}
        let form = form_from_sig(&sig, 2);
        let e = cleanup_anf(&form);
        assert_eq!(evaluate_boolean_signature(&e, 2, 1), sig);
        // Should be `x & ~y` — an AND node with a NOT leaf.
        assert!(matches!(e.kind, Kind::And));
    }

    #[test]
    fn from_packed_anf_round_trip_preserves_evaluation() {
        // For every 3-var Boolean function, ANF → cleanup → eval must
        // match the original signature at bitwidth 1.
        for key in 0u8..=255 {
            let sig: Vec<u64> = (0..8).map(|i| u64::from((key >> i) & 1)).collect();
            let form = form_from_sig(&sig, 3);
            let e = cleanup_anf(&form);
            let recovered = evaluate_boolean_signature(&e, 3, 1);
            assert_eq!(recovered, sig, "key 0x{key:X} round-trip failed");
        }
    }

    #[test]
    fn anf_expr_cost_or_depth_discount() {
        // Left-associative or(or(a, b), c) has chain depth 2 → the
        // discount fires and cost drops by 1 (raw 5 → discounted 4).
        // Right-associative or(a, or(b, c)) has depth 1 so the discount
        // does NOT fire — raw cost stands at 5.
        let left_assoc = Expr::or(
            Expr::or(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        assert_eq!(anf_expr_cost(&left_assoc), 4);

        let right_assoc = Expr::or(
            Expr::variable(0),
            Expr::or(Expr::variable(1), Expr::variable(2)),
        );
        assert_eq!(anf_expr_cost(&right_assoc), 5);
    }
}
