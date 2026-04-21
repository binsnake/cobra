//! Lower an [`Expr`] into its [`SemilinearIR`] form: a weighted sum of
//! pure-bitwise atoms plus a constant. Works by a single bottom-up
//! walk that (a) lowers constant-operand XOR / OR / (~a)&c patterns
//! into AND-basis, (b) registers pure-bitwise subtrees with variables
//! as atoms, and (c) folds constant-only subtrees into the running
//! coefficient.
//!
//! Any `var * var` multiplication or shift of a non-bitwise operand
//! makes the input non-semilinear — the function returns
//! [`CobraError::NonLinearInput`] in that case.

use std::collections::HashMap;

use cobra_core::arith::{bitmask, mod_neg, mod_shr};
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_utils::has_var_dep;
use cobra_core::result::{err, CobraError, Result};

use crate::semilinear::{
    compute_atom_truth_table, structural_hash, AtomId, AtomInfo, AtomKey, GlobalVarIdx,
    OperatorFamily, SemilinearIR, WeightedAtom,
};

fn is_purely_bitwise(expr: &Expr) -> bool {
    match expr.kind {
        Kind::Constant(_) | Kind::Variable(_) => true,
        Kind::And | Kind::Or | Kind::Xor => {
            is_purely_bitwise(&expr.children[0]) && is_purely_bitwise(&expr.children[1])
        }
        Kind::Not | Kind::Shr(_) => is_purely_bitwise(&expr.children[0]),
        Kind::Add | Kind::Mul | Kind::Neg => false,
    }
}

fn has_constant(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Constant(_)) {
        return true;
    }
    expr.children.iter().any(|c| has_constant(c))
}

fn contains_shr(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Shr(_)) {
        return true;
    }
    expr.children.iter().any(|c| contains_shr(c))
}

fn eval_constant_bitwise(expr: &Expr, mask: u64) -> u64 {
    match &expr.kind {
        Kind::Constant(v) => *v & mask,
        Kind::And => {
            eval_constant_bitwise(&expr.children[0], mask)
                & eval_constant_bitwise(&expr.children[1], mask)
        }
        Kind::Or => {
            eval_constant_bitwise(&expr.children[0], mask)
                | eval_constant_bitwise(&expr.children[1], mask)
        }
        Kind::Xor => {
            eval_constant_bitwise(&expr.children[0], mask)
                ^ eval_constant_bitwise(&expr.children[1], mask)
        }
        Kind::Not => (!eval_constant_bitwise(&expr.children[0], mask)) & mask,
        Kind::Shr(k) => {
            let v = eval_constant_bitwise(&expr.children[0], mask);
            mod_shr(v, u64::from(*k), 64) & mask
        }
        _ => 0,
    }
}

fn eval_constant_arith(expr: &Expr, mask: u64, bitwidth: u32) -> u64 {
    match &expr.kind {
        Kind::Constant(v) => *v & mask,
        Kind::Neg => {
            let v = eval_constant_arith(&expr.children[0], mask, bitwidth);
            mod_neg(v, bitwidth)
        }
        Kind::Add => {
            let l = eval_constant_arith(&expr.children[0], mask, bitwidth);
            let r = eval_constant_arith(&expr.children[1], mask, bitwidth);
            l.wrapping_add(r) & mask
        }
        Kind::Mul => {
            let l = eval_constant_arith(&expr.children[0], mask, bitwidth);
            let r = eval_constant_arith(&expr.children[1], mask, bitwidth);
            l.wrapping_mul(r) & mask
        }
        Kind::Shr(k) => {
            let v = eval_constant_arith(&expr.children[0], mask, bitwidth);
            mod_shr(v, u64::from(*k), 64) & mask
        }
        Kind::And | Kind::Or | Kind::Xor | Kind::Not => eval_constant_bitwise(expr, mask),
        Kind::Variable(_) => 0,
    }
}

#[allow(clippy::match_same_arms)]
fn detect_provenance(expr: &Expr) -> OperatorFamily {
    match expr.kind {
        Kind::Constant(_) | Kind::Variable(_) => OperatorFamily::Mixed,
        Kind::Not => OperatorFamily::Not,
        Kind::And => {
            let l = detect_provenance(&expr.children[0]);
            let r = detect_provenance(&expr.children[1]);
            if matches!(l, OperatorFamily::And | OperatorFamily::Mixed)
                && matches!(r, OperatorFamily::And | OperatorFamily::Mixed)
            {
                OperatorFamily::And
            } else {
                OperatorFamily::Mixed
            }
        }
        Kind::Or => {
            let l = detect_provenance(&expr.children[0]);
            let r = detect_provenance(&expr.children[1]);
            if matches!(l, OperatorFamily::Or | OperatorFamily::Mixed)
                && matches!(r, OperatorFamily::Or | OperatorFamily::Mixed)
            {
                OperatorFamily::Or
            } else {
                OperatorFamily::Mixed
            }
        }
        Kind::Xor => {
            let l = detect_provenance(&expr.children[0]);
            let r = detect_provenance(&expr.children[1]);
            if matches!(l, OperatorFamily::Xor | OperatorFamily::Mixed)
                && matches!(r, OperatorFamily::Xor | OperatorFamily::Mixed)
            {
                OperatorFamily::Xor
            } else {
                OperatorFamily::Mixed
            }
        }
        _ => OperatorFamily::Mixed,
    }
}

fn collect_support(expr: &Expr, out: &mut Vec<GlobalVarIdx>) {
    if let Kind::Variable(i) = expr.kind {
        out.push(i);
        return;
    }
    for c in &expr.children {
        collect_support(c, out);
    }
}

struct CollectCtx {
    bitwidth: u32,
    mask: u64,
    atom_map: HashMap<AtomKey, AtomId>,
    atom_table: Vec<AtomInfo>,
    hash_cache: HashMap<u64, AtomId>,
    encountered_nonlinear: bool,
}

struct CollectResult {
    constant: u64,
    terms: Vec<WeightedAtom>,
}

fn register_atom(ctx: &mut CollectCtx, expr: &Expr) -> AtomId {
    let mut support = Vec::new();
    collect_support(expr, &mut support);
    support.sort_unstable();
    support.dedup();

    let struct_hash = structural_hash(expr);

    if let Some(&existing) = ctx.hash_cache.get(&struct_hash) {
        if ctx.atom_table[existing as usize].key.support == support {
            return existing;
        }
    }

    let tt = compute_atom_truth_table(expr, &support, ctx.bitwidth);
    let key = AtomKey {
        support,
        truth_table: tt,
    };

    let pure = !has_constant(expr) && !contains_shr(expr);
    if pure && !key.truth_table.is_empty() {
        if let Some(&id) = ctx.atom_map.get(&key) {
            return id;
        }
    }

    let atom_id = ctx.atom_table.len() as AtomId;
    if pure && !key.truth_table.is_empty() {
        ctx.atom_map.insert(key.clone(), atom_id);
    }
    ctx.hash_cache.insert(struct_hash, atom_id);

    ctx.atom_table.push(AtomInfo {
        atom_id,
        key,
        structural_hash: struct_hash,
        original_subtree: expr.clone_tree(),
        provenance: detect_provenance(expr),
    });
    atom_id
}

#[allow(clippy::too_many_lines)]
fn collect_terms(ctx: &mut CollectCtx, expr: &Expr, coeff: u64) -> CollectResult {
    let coeff = coeff & ctx.mask;
    if coeff == 0 {
        return CollectResult {
            constant: 0,
            terms: Vec::new(),
        };
    }

    // Lower XOR/OR with a constant operand to AND basis:
    //   a ^ c = a + c - 2*(a & c)
    //   a | c =  a + c - (a & c)
    if matches!(expr.kind, Kind::Xor | Kind::Or) && is_purely_bitwise(expr) && has_var_dep(expr) {
        let lhs_const = !has_var_dep(&expr.children[0]);
        let rhs_const = !has_var_dep(&expr.children[1]);
        if lhs_const || rhs_const {
            let (const_child, var_child) = if lhs_const {
                (&expr.children[0], &expr.children[1])
            } else {
                (&expr.children[1], &expr.children[0])
            };
            let c = eval_constant_bitwise(const_child, ctx.mask);
            let mut var_result = collect_terms(ctx, var_child, coeff);
            var_result.constant =
                var_result.constant.wrapping_add(coeff.wrapping_mul(c)) & ctx.mask;

            let and_expr = Expr::and(var_child.clone_tree(), Expr::constant(c));
            let and_coeff = if matches!(expr.kind, Kind::Xor) {
                mod_neg(coeff.wrapping_mul(2) & ctx.mask, ctx.bitwidth)
            } else {
                mod_neg(coeff, ctx.bitwidth)
            };
            let and_result = collect_terms(ctx, &and_expr, and_coeff);
            var_result.constant = var_result.constant.wrapping_add(and_result.constant) & ctx.mask;
            var_result.terms.extend(and_result.terms);
            return var_result;
        }
    }

    // Lower (~a) & c = c - (a & c) when a has variables.
    if matches!(expr.kind, Kind::And) && is_purely_bitwise(expr) && has_var_dep(expr) {
        for side in 0..2 {
            let lhs = &expr.children[side];
            let rhs = &expr.children[1 - side];
            if !matches!(lhs.kind, Kind::Not) {
                continue;
            }
            if !has_var_dep(lhs) || has_var_dep(rhs) {
                continue;
            }
            let inner = &lhs.children[0];
            let c = eval_constant_bitwise(rhs, ctx.mask);
            let and_expr = Expr::and(inner.clone_tree(), Expr::constant(c));
            let and_aid = register_atom(ctx, &and_expr);
            let and_coeff = mod_neg(coeff, ctx.bitwidth);
            let const_part = coeff.wrapping_mul(c) & ctx.mask;
            return CollectResult {
                constant: const_part,
                terms: vec![WeightedAtom {
                    coeff: and_coeff,
                    atom_id: and_aid,
                }],
            };
        }
    }

    if is_purely_bitwise(expr) && has_var_dep(expr) {
        let aid = register_atom(ctx, expr);
        return CollectResult {
            constant: 0,
            terms: vec![WeightedAtom {
                coeff,
                atom_id: aid,
            }],
        };
    }

    if !has_var_dep(expr) {
        let v = eval_constant_arith(expr, ctx.mask, ctx.bitwidth);
        return CollectResult {
            constant: coeff.wrapping_mul(v) & ctx.mask,
            terms: Vec::new(),
        };
    }

    match &expr.kind {
        Kind::Add => {
            let l = collect_terms(ctx, &expr.children[0], coeff);
            let r = collect_terms(ctx, &expr.children[1], coeff);
            let c = l.constant.wrapping_add(r.constant) & ctx.mask;
            let mut terms = l.terms;
            terms.extend(r.terms);
            CollectResult { constant: c, terms }
        }
        Kind::Neg => {
            let neg = mod_neg(coeff, ctx.bitwidth);
            collect_terms(ctx, &expr.children[0], neg)
        }
        Kind::Mul => {
            let lhs_const = !has_var_dep(&expr.children[0]);
            let rhs_const = !has_var_dep(&expr.children[1]);
            if lhs_const {
                let c = eval_constant_arith(&expr.children[0], ctx.mask, ctx.bitwidth);
                return collect_terms(ctx, &expr.children[1], coeff.wrapping_mul(c) & ctx.mask);
            }
            if rhs_const {
                let c = eval_constant_arith(&expr.children[1], ctx.mask, ctx.bitwidth);
                return collect_terms(ctx, &expr.children[0], coeff.wrapping_mul(c) & ctx.mask);
            }
            ctx.encountered_nonlinear = true;
            CollectResult {
                constant: 0,
                terms: Vec::new(),
            }
        }
        Kind::Shr(_) => {
            if is_purely_bitwise(expr) && has_var_dep(expr) {
                let aid = register_atom(ctx, expr);
                return CollectResult {
                    constant: 0,
                    terms: vec![WeightedAtom {
                        coeff,
                        atom_id: aid,
                    }],
                };
            }
            if !has_var_dep(expr) {
                let v = eval_constant_arith(expr, ctx.mask, ctx.bitwidth);
                return CollectResult {
                    constant: coeff.wrapping_mul(v) & ctx.mask,
                    terms: Vec::new(),
                };
            }
            ctx.encountered_nonlinear = true;
            CollectResult {
                constant: 0,
                terms: Vec::new(),
            }
        }
        Kind::And | Kind::Or | Kind::Xor | Kind::Not => {
            ctx.encountered_nonlinear = true;
            CollectResult {
                constant: 0,
                terms: Vec::new(),
            }
        }
        _ => CollectResult {
            constant: 0,
            terms: Vec::new(),
        },
    }
}

/// Normalise `expr` into [`SemilinearIR`] form. Panics on invalid
/// bitwidth only indirectly via [`bitmask`]. Returns
/// [`CobraError::NonLinearInput`] when a `var * var` multiplication or
/// shift of a non-bitwise operand is encountered.
pub fn normalize_to_semilinear(
    expr: &Expr,
    _vars: &[String],
    bitwidth: u32,
) -> Result<SemilinearIR> {
    let mut ctx = CollectCtx {
        bitwidth,
        mask: bitmask(bitwidth),
        atom_map: HashMap::new(),
        atom_table: Vec::new(),
        hash_cache: HashMap::new(),
        encountered_nonlinear: false,
    };
    let result = collect_terms(&mut ctx, expr, 1);
    if ctx.encountered_nonlinear {
        return Err(err(
            CobraError::NonLinearInput,
            "expression is not semilinear (variable*variable multiplication or shift of non-bitwise operand)",
        ));
    }

    let mut coeff_map: HashMap<AtomId, u64> = HashMap::new();
    for t in &result.terms {
        let slot = coeff_map.entry(t.atom_id).or_insert(0);
        *slot = slot.wrapping_add(t.coeff) & ctx.mask;
    }

    let mut ir = SemilinearIR {
        constant: result.constant & ctx.mask,
        bitwidth,
        atom_table: ctx.atom_table,
        terms: Vec::new(),
    };

    let mut sorted: Vec<(AtomId, u64)> = coeff_map.into_iter().filter(|&(_, c)| c != 0).collect();
    sorted.sort_by_key(|(id, _)| *id);
    ir.terms = sorted
        .into_iter()
        .map(|(atom_id, coeff)| WeightedAtom { coeff, atom_id })
        .collect();
    Ok(ir)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_linear_expression() {
        // f = 3*x + 5*y + 7 — two atoms, constant = 7.
        let expr = Expr::add(
            Expr::add(
                Expr::mul(Expr::constant(3), Expr::variable(0)),
                Expr::mul(Expr::constant(5), Expr::variable(1)),
            ),
            Expr::constant(7),
        );
        let ir = normalize_to_semilinear(&expr, &["x".into(), "y".into()], 64).unwrap();
        assert_eq!(ir.constant, 7);
        assert_eq!(ir.terms.len(), 2);
    }

    #[test]
    fn pure_bitwise_with_variable_becomes_single_atom() {
        // f = x & y
        let expr = Expr::and(Expr::variable(0), Expr::variable(1));
        let ir = normalize_to_semilinear(&expr, &["x".into(), "y".into()], 64).unwrap();
        assert_eq!(ir.terms.len(), 1);
        assert_eq!(ir.terms[0].coeff, 1);
        assert_eq!(ir.atom_table.len(), 1);
    }

    #[test]
    fn xor_with_constant_lowers_to_and_basis() {
        // f = x ^ 0xFF — should normalize to x + 0xFF - 2*(x & 0xFF).
        let expr = Expr::xor(Expr::variable(0), Expr::constant(0xFF));
        let ir = normalize_to_semilinear(&expr, &["x".into()], 64).unwrap();
        // Constant contribution: 0xFF
        assert_eq!(ir.constant, 0xFF);
        assert_eq!(ir.terms.len(), 2);
    }

    #[test]
    fn var_times_var_is_non_linear() {
        let expr = Expr::mul(Expr::variable(0), Expr::variable(1));
        let res = normalize_to_semilinear(&expr, &["x".into(), "y".into()], 64);
        assert!(res.is_err());
    }

    #[test]
    fn constant_folds_into_constant() {
        let expr = Expr::add(Expr::constant(10), Expr::constant(32));
        let ir = normalize_to_semilinear(&expr, &[], 64).unwrap();
        assert_eq!(ir.constant, 42);
        assert!(ir.terms.is_empty());
    }

    #[test]
    fn duplicate_atoms_get_coefficients_summed() {
        // f = x + x → single atom with coefficient 2.
        let expr = Expr::add(Expr::variable(0), Expr::variable(0));
        let ir = normalize_to_semilinear(&expr, &["x".into()], 64).unwrap();
        assert_eq!(ir.terms.len(), 1);
        assert_eq!(ir.terms[0].coeff, 2);
    }
}
