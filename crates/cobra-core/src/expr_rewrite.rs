//! already in [`crate::expr_utils`].

// `std::unique_ptr<Expr>`. The flatten/rebuild helpers below keep trees in
// their boxed form to avoid deep copies when reshuffling nodes.
#![allow(clippy::vec_box)]

use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

use crate::arith::{bitmask, mod_add};
use crate::expr::{Expr, Kind};
use crate::expr_utils::{eval_constant, has_var_dep, is_constant_subtree};

/// Build a left-leaning `And` product from the variables whose bit is set
/// expected to handle this case).
#[must_use]
pub fn build_and_product(mut mask: u64) -> Option<Box<Expr>> {
    let mut result: Option<Box<Expr>> = None;
    while mask != 0 {
        let bit = mask.trailing_zeros();
        let var = Expr::variable(bit);
        result = Some(match result {
            None => var,
            Some(acc) => Expr::and(acc, var),
        });
        mask &= mask - 1;
    }
    result
}

/// Apply a multiplicative coefficient to an expression:
/// `1 * e → e`, `-1 * e → -e`, otherwise `c * e`.
#[must_use]
pub fn apply_coefficient(expr: Box<Expr>, coeff: u64, bitwidth: u32) -> Box<Expr> {
    if coeff == 1 {
        return expr;
    }
    if coeff == bitmask(bitwidth) {
        return Expr::neg(expr);
    }
    Expr::mul(Expr::constant(coeff), expr)
}

/// Map each name in `subset_vars` to its position in `all_vars`. Panics if
#[must_use]
pub fn build_var_support(all_vars: &[String], subset_vars: &[String]) -> Vec<u32> {
    let mut idx: HashMap<&str, u32> = HashMap::with_capacity(all_vars.len());
    for (j, v) in all_vars.iter().enumerate() {
        idx.insert(v.as_str(), j as u32);
    }
    subset_vars
        .iter()
        .map(|v| *idx.get(v.as_str()).expect("variable not in all_vars"))
        .collect()
}

/// Non-panicking variant: returns `None` when any `subset_vars` name
/// is missing from `all_vars`. Callers that route candidates up from
/// residual / lifted-outer contexts (where the reduced var set may
/// live in a different namespace than `ctx.original_vars`) use this
/// to skip the remap gracefully instead of panicking.
#[must_use]
pub fn try_build_var_support(all_vars: &[String], subset_vars: &[String]) -> Option<Vec<u32>> {
    let mut idx: HashMap<&str, u32> = HashMap::with_capacity(all_vars.len());
    for (j, v) in all_vars.iter().enumerate() {
        idx.insert(v.as_str(), j as u32);
    }
    subset_vars
        .iter()
        .map(|v| idx.get(v.as_str()).copied())
        .collect()
}

/// `true` if any non-leaf bitwise node (`And`/`Or`/`Xor`/`Not`) depends on
/// a variable. Used by the pass layer to detect "real" bitwise structure.
#[must_use]
pub fn has_nonleaf_bitwise(expr: &Expr) -> bool {
    let self_matches =
        matches!(expr.kind, Kind::And | Kind::Or | Kind::Xor | Kind::Not) && has_var_dep(expr);
    if self_matches {
        return true;
    }
    expr.children.iter().any(|c| has_nonleaf_bitwise(c))
}

/// Replace `AND(var-dep, var-dep)` with `MUL` wherever both sides are pure
/// `Variable`/`And`/`Mul` compositions. This corrects the product-shadow
#[must_use]
pub fn repair_product_shadow(mut expr: Box<Expr>) -> Box<Expr> {
    let mut new_children = expr
        .children
        .drain(..)
        .map(repair_product_shadow)
        .collect::<smallvec::SmallVec<[Box<Expr>; 2]>>();

    expr.children = new_children.drain(..).collect();

    if matches!(expr.kind, Kind::And)
        && expr.children.len() == 2
        && is_pure_product(&expr.children[0])
        && is_pure_product(&expr.children[1])
    {
        let mut it = expr.children.into_iter();
        let lhs = it.next().unwrap();
        let rhs = it.next().unwrap();
        return Expr::mul(lhs, rhs);
    }
    expr
}

fn is_pure_product(e: &Expr) -> bool {
    match e.kind {
        Kind::Variable(_) => true,
        Kind::And | Kind::Mul => e.children.iter().all(|c| is_pure_product(c)),
        _ => false,
    }
}

/// Cosmetic cleanup on a simplified expression: constant folding followed
/// by `-x + (2^n - 1)` → `~x` refolding followed by common-factor extraction.
/// Semantics-preserving, so no verification step is required.
#[must_use]
pub fn cleanup_final_expr(mut expr: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    expr = fold_constant_arithmetic(expr, bitwidth);
    expr = refold_negation(expr, bitwidth);
    expr = extract_common_factor(expr);
    expr = fold_constant_arithmetic(expr, bitwidth);
    expr
}

// ---------- private cleanup helpers ----------

fn flatten_add(node: Box<Expr>, terms: &mut Vec<Box<Expr>>) {
    if matches!(node.kind, Kind::Add) {
        let mut node = node;
        let mut it = node.children.drain(..);
        let lhs = it.next().unwrap();
        let rhs = it.next().unwrap();
        drop(it);
        flatten_add(lhs, terms);
        flatten_add(rhs, terms);
    } else {
        terms.push(node);
    }
}

fn flatten_mul(node: Box<Expr>, factors: &mut Vec<Box<Expr>>) {
    if matches!(node.kind, Kind::Mul) {
        let mut node = node;
        let mut it = node.children.drain(..);
        let lhs = it.next().unwrap();
        let rhs = it.next().unwrap();
        drop(it);
        flatten_mul(lhs, factors);
        flatten_mul(rhs, factors);
    } else {
        factors.push(node);
    }
}

fn rebuild_mul(factors: Vec<Box<Expr>>) -> Box<Expr> {
    let mut it = factors.into_iter();
    let mut result = it.next().expect("rebuild_mul requires >= 1 factor");
    for f in it {
        result = Expr::mul(result, f);
    }
    result
}

fn fold_constant_arithmetic(mut expr: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    // Recurse first so children are folded before we inspect the current node.
    let children: Vec<Box<Expr>> = expr
        .children
        .drain(..)
        .map(|c| fold_constant_arithmetic(c, bitwidth))
        .collect();
    expr.children = children.into_iter().collect();

    if is_constant_subtree(&expr) && !matches!(expr.kind, Kind::Constant(_)) {
        return Expr::constant(eval_constant(&expr, bitwidth));
    }

    if !matches!(expr.kind, Kind::Add) {
        return expr;
    }

    // Flatten Add chains and re-combine constant terms.
    let mut terms: Vec<Box<Expr>> = Vec::new();
    flatten_add(expr, &mut terms);

    let mut const_sum: u64 = 0;
    let mut non_const: Vec<Box<Expr>> = Vec::new();
    for t in terms {
        if let Kind::Constant(v) = t.kind {
            const_sum = mod_add(const_sum, v, bitwidth);
        } else {
            non_const.push(t);
        }
    }

    if non_const.is_empty() {
        return Expr::constant(const_sum);
    }

    let mut it = non_const.into_iter();
    let mut result = it.next().unwrap();
    for next in it {
        result = Expr::add(result, next);
    }
    if const_sum != 0 {
        result = Expr::add(result, Expr::constant(const_sum));
    }
    result
}

fn refold_negation(mut expr: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    let children: Vec<Box<Expr>> = expr
        .children
        .drain(..)
        .map(|c| refold_negation(c, bitwidth))
        .collect();
    expr.children = children.into_iter().collect();

    if !matches!(expr.kind, Kind::Add) {
        return expr;
    }
    let mask = bitmask(bitwidth);
    let lhs_is_neg = matches!(expr.children[0].kind, Kind::Neg);
    let rhs_is_const_all_ones = matches!(&expr.children[1].kind, Kind::Constant(v) if *v == mask);
    let rhs_is_neg = matches!(expr.children[1].kind, Kind::Neg);
    let lhs_is_const_all_ones = matches!(&expr.children[0].kind, Kind::Constant(v) if *v == mask);

    if lhs_is_neg && rhs_is_const_all_ones {
        let mut lhs = expr.children.remove(0); // Neg(x)
        let inner = lhs.children.remove(0);
        return Expr::not(inner);
    }
    if rhs_is_neg && lhs_is_const_all_ones {
        let mut rhs = expr.children.remove(1);
        let inner = rhs.children.remove(0);
        return Expr::not(inner);
    }
    expr
}

#[allow(clippy::too_many_lines)]
fn extract_common_factor(mut expr: Box<Expr>) -> Box<Expr> {
    let children: Vec<Box<Expr>> = expr.children.drain(..).map(extract_common_factor).collect();
    expr.children = children.into_iter().collect();

    if !matches!(expr.kind, Kind::Add) {
        return expr;
    }

    let mut terms: Vec<Box<Expr>> = Vec::new();
    flatten_add(expr, &mut terms);
    if terms.len() < 2 {
        return terms.pop().unwrap_or_else(|| Expr::constant(0));
    }

    let mut all_factors: Vec<Vec<Box<Expr>>> = Vec::with_capacity(terms.len());
    for t in terms {
        let mut factors = Vec::new();
        if matches!(t.kind, Kind::Mul) {
            flatten_mul(t, &mut factors);
        } else {
            factors.push(t);
        }
        all_factors.push(factors);
    }

    // Hash every factor once. For each term, build a map from factor hash
    // to the list of factor indices sharing that hash. A candidate common
    // factor is one whose hash appears in every term's map; we then verify
    // with structural equality to guard against collisions.
    let factor_hashes: Vec<Vec<u64>> = all_factors
        .iter()
        .map(|fs| fs.iter().map(|f| expr_hash(f)).collect())
        .collect();
    let per_term_maps: Vec<HashMap<u64, Vec<usize>>> = factor_hashes
        .iter()
        .map(|hs| {
            let mut m: HashMap<u64, Vec<usize>> = HashMap::with_capacity(hs.len());
            for (i, h) in hs.iter().enumerate() {
                m.entry(*h).or_default().push(i);
            }
            m
        })
        .collect();

    // For each non-constant, non-bare-variable factor of the first term,
    // check whether its hash is present in every other term and, if so,
    // verify a structurally-equal match exists. The first such universal
    // factor wins; extract it and recurse on the remainder.
    for fi in 0..all_factors[0].len() {
        let kind_matches = {
            let c = &all_factors[0][fi];
            !matches!(c.kind, Kind::Constant(_) | Kind::Variable(_))
        };
        if !kind_matches {
            continue;
        }
        let candidate_hash = factor_hashes[0][fi];
        let candidate = &all_factors[0][fi];
        let candidate_discriminant = std::mem::discriminant(&candidate.kind);

        let mut match_indices: Vec<usize> = vec![fi];
        let mut universal = true;
        for ti in 1..all_factors.len() {
            let Some(bucket) = per_term_maps[ti].get(&candidate_hash) else {
                universal = false;
                break;
            };
            let mut found: Option<usize> = None;
            for &fj in bucket {
                let f = &all_factors[ti][fj];
                if matches!(f.kind, Kind::Constant(_)) {
                    continue;
                }
                if std::mem::discriminant(&f.kind) == candidate_discriminant && **f == **candidate {
                    found = Some(fj);
                    break;
                }
            }
            if let Some(fj) = found {
                match_indices.push(fj);
            } else {
                universal = false;
                break;
            }
        }

        if !universal {
            continue;
        }

        let common = all_factors[0].remove(fi);

        let mut remainders: Vec<Box<Expr>> = Vec::with_capacity(all_factors.len());
        for (ti, factors) in all_factors.iter_mut().enumerate() {
            if ti == 0 {
                // fi already removed above
            } else {
                let idx = match_indices[ti];
                factors.remove(idx);
            }
            if factors.is_empty() {
                remainders.push(Expr::constant(1));
            } else {
                remainders.push(rebuild_mul(std::mem::take(factors)));
            }
        }

        let mut it = remainders.into_iter();
        let mut sum = it.next().unwrap();
        for next in it {
            sum = Expr::add(sum, next);
        }
        sum = extract_common_factor(sum);
        return Expr::mul(sum, common);
    }

    let mut rebuilt: Vec<Box<Expr>> = all_factors.into_iter().map(rebuild_mul).collect();
    let mut it = rebuilt.drain(..);
    let mut result = it.next().unwrap();
    for next in it {
        result = Expr::add(result, next);
    }
    result
}

fn expr_hash(e: &Expr) -> u64 {
    let mut h = DefaultHasher::new();
    e.hash(&mut h);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval_at(expr: &Expr, vals: &[u64], bitwidth: u32) -> u64 {
        use crate::compiled::{compile, eval};
        let c = compile(expr, bitwidth);
        let mut stack = Vec::new();
        eval(&c, vals, &mut stack)
    }

    #[test]
    fn build_and_product_empty() {
        assert!(build_and_product(0).is_none());
    }

    #[test]
    fn build_and_product_single_bit() {
        let e = build_and_product(0b100).unwrap();
        // Only variable v2, no And
        assert!(matches!(e.kind, Kind::Variable(2)));
    }

    #[test]
    fn build_and_product_multiple_bits() {
        // bits 0, 2, 5 → ((v0 & v2) & v5)
        let e = build_and_product(0b10_0101).unwrap();
        assert!(matches!(e.kind, Kind::And));
        // Evaluated at v0=v2=v5=1 (all others 0): should be 1
        let mut vals = vec![0u64; 6];
        vals[0] = 1;
        vals[2] = 1;
        vals[5] = 1;
        assert_eq!(eval_at(&e, &vals, 64), 1);
        // Any of them zero → 0
        vals[2] = 0;
        assert_eq!(eval_at(&e, &vals, 64), 0);
    }

    #[test]
    fn apply_coefficient_one_is_identity() {
        let e = Expr::variable(0);
        let out = apply_coefficient(e.clone(), 1, 64);
        assert_eq!(&*out, &*e);
    }

    #[test]
    fn apply_coefficient_minus_one_is_neg() {
        let out = apply_coefficient(Expr::variable(0), u64::MAX, 64);
        assert!(matches!(out.kind, Kind::Neg));
    }

    #[test]
    fn apply_coefficient_other_is_mul_with_constant_on_lhs() {
        let out = apply_coefficient(Expr::variable(0), 3, 64);
        assert!(matches!(out.kind, Kind::Mul));
        assert!(matches!(out.children[0].kind, Kind::Constant(3)));
    }

    #[test]
    fn build_var_support_maps_subset() {
        let all = vec![
            "a".to_owned(),
            "b".to_owned(),
            "c".to_owned(),
            "d".to_owned(),
        ];
        let subset = vec!["c".to_owned(), "a".to_owned()];
        assert_eq!(build_var_support(&all, &subset), vec![2, 0]);
    }

    #[test]
    fn has_nonleaf_bitwise_detects() {
        assert!(has_nonleaf_bitwise(&Expr::and(
            Expr::variable(0),
            Expr::variable(1)
        )));
        assert!(has_nonleaf_bitwise(&Expr::not(Expr::variable(0))));
        // Pure arithmetic: no bitwise
        assert!(!has_nonleaf_bitwise(&Expr::add(
            Expr::variable(0),
            Expr::variable(1)
        )));
        // Bitwise with no var dependence: rejected
        assert!(!has_nonleaf_bitwise(&Expr::and(
            Expr::constant(3),
            Expr::constant(5)
        )));
    }

    #[test]
    fn repair_product_shadow_rewrites_pure_and() {
        let e = Expr::and(Expr::variable(0), Expr::variable(1));
        let repaired = repair_product_shadow(e);
        assert!(matches!(repaired.kind, Kind::Mul));
    }

    #[test]
    fn repair_product_shadow_leaves_mixed_alone() {
        // AND(x, y+z) — rhs is not a pure product, leave as-is
        let e = Expr::and(
            Expr::variable(0),
            Expr::add(Expr::variable(1), Expr::variable(2)),
        );
        let repaired = repair_product_shadow(e);
        assert!(matches!(repaired.kind, Kind::And));
    }

    #[test]
    fn cleanup_folds_constants() {
        // 1 + 2 + a → a + 3 (order may differ)
        let e = Expr::add(
            Expr::add(Expr::constant(1), Expr::constant(2)),
            Expr::variable(0),
        );
        let cleaned = cleanup_final_expr(e, 64);
        // Must evaluate to a + 3 on any input
        assert_eq!(eval_at(&cleaned, &[0], 64), 3);
        assert_eq!(eval_at(&cleaned, &[5], 64), 8);
    }

    #[test]
    fn cleanup_refolds_neg_plus_all_ones_to_not() {
        // bitwidth 8: -a + 0xFF → ~a
        let e = Expr::add(Expr::neg(Expr::variable(0)), Expr::constant(0xFF));
        let cleaned = cleanup_final_expr(e, 8);
        for v in [0u64, 1, 7, 0x55, 0xFF] {
            assert_eq!(eval_at(&cleaned, &[v], 8), !v & 0xFF);
        }
    }

    #[test]
    fn cleanup_extracts_common_factor() {
        // a*c + b*c → (a + b) * c
        let e = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(2)),
            Expr::mul(Expr::variable(1), Expr::variable(2)),
        );
        let cleaned = cleanup_final_expr(e, 64);
        // Verify it still evaluates correctly
        for (a, b, c) in [(1u64, 2, 3), (5, 7, 11), (0, 3, 4)] {
            let vals = vec![a, b, c];
            assert_eq!(eval_at(&cleaned, &vals, 64), (a + b).wrapping_mul(c));
        }
    }
}
