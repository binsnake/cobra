//! Bitwise decomposer: cofactor the signature on each variable and
//! match the result against one of the five gate templates
//! (`AND`, `OR`, `XOR`, `MUL`, `ADD` with additive coefficient).
//!
//! For variable `k`, `cof0[i] = sig[i]` where bit `k` of `i` is 0,
//! `cof1[i] = sig[i | (1<<k)]`. The match rules:
//!
//! - `cof0 == 0` → `AND(x_k, cof1)` (when `cof1` is Boolean) and
//!   `MUL(x_k, cof1)` unconditionally
//! - `cof1 == cof0 | 1` → `OR(x_k, cof0)`
//! - `cof1 == cof0 ^ 1` → `XOR(x_k, cof0)`
//! - `cof1 - cof0 == const != 0` → `ADD(const * x_k, cof0)`
//!
//! Results are sorted ascending by residual active-variable count.

use cobra_core::expr::{Expr, Kind};

use cobra_orchestrator::GateKind;

#[derive(Clone, Debug)]
pub struct BitwiseSplitCandidate {
    pub var_k: u32,
    pub gate: GateKind,
    pub g_sig: Vec<u64>,
    pub add_coeff: u64,
    pub active_count: u32,
}

/// Count variables whose flipping changes at least one signature
/// entry.
#[must_use]
pub fn count_active(sig: &[u64], n: u32) -> u32 {
    let mut count = 0;
    for v in 0..n {
        let mut active = false;
        for j in 0..sig.len() {
            let flipped = j ^ (1usize << v);
            if sig[j] != sig[flipped] {
                active = true;
                break;
            }
        }
        if active {
            count += 1;
        }
    }
    count
}

/// Compact a signature to only its active variables. Returns
/// `(compacted_sig, active_var_indices)`. A signature with no active
/// variables returns `(vec![sig[0]], vec![])`.
#[must_use]
pub fn compact_signature(sig: &[u64], n: u32) -> (Vec<u64>, Vec<u32>) {
    let mut active_vars: Vec<u32> = Vec::new();
    for v in 0..n {
        for j in 0..sig.len() {
            let flipped = j ^ (1usize << v);
            if sig[j] != sig[flipped] {
                active_vars.push(v);
                break;
            }
        }
    }
    if active_vars.is_empty() {
        return (vec![sig[0]], Vec::new());
    }
    let n_active = active_vars.len() as u32;
    let mut compacted = vec![0u64; 1usize << n_active];
    for ci in 0..(1u32 << n_active) {
        let mut orig_idx = 0u32;
        for (a, &var) in active_vars.iter().enumerate() {
            if ((ci >> a) & 1) != 0 {
                orig_idx |= 1u32 << var;
            }
        }
        compacted[ci as usize] = sig[orig_idx as usize];
    }
    (compacted, active_vars)
}

/// Remap variable indices in `expr` using `index_map` (compacted index
/// → original index). Returns a fresh tree; the input is not modified.
#[must_use]
pub fn remap_vars(expr: &Expr, index_map: &[u32]) -> Box<Expr> {
    match &expr.kind {
        Kind::Constant(v) => Expr::constant(*v),
        Kind::Variable(i) => Expr::variable(index_map[*i as usize]),
        Kind::Add => Expr::add(
            remap_vars(&expr.children[0], index_map),
            remap_vars(&expr.children[1], index_map),
        ),
        Kind::Mul => Expr::mul(
            remap_vars(&expr.children[0], index_map),
            remap_vars(&expr.children[1], index_map),
        ),
        Kind::And => Expr::and(
            remap_vars(&expr.children[0], index_map),
            remap_vars(&expr.children[1], index_map),
        ),
        Kind::Or => Expr::or(
            remap_vars(&expr.children[0], index_map),
            remap_vars(&expr.children[1], index_map),
        ),
        Kind::Xor => Expr::xor(
            remap_vars(&expr.children[0], index_map),
            remap_vars(&expr.children[1], index_map),
        ),
        Kind::Not => Expr::not(remap_vars(&expr.children[0], index_map)),
        Kind::Neg => Expr::neg(remap_vars(&expr.children[0], index_map)),
        Kind::Shr(k) => Expr::shr(remap_vars(&expr.children[0], index_map), u64::from(*k)),
    }
}

/// Compose `gate(x_k, g_expr)` with the ADD gate taking an optional
/// coefficient on `x_k`.
#[must_use]
pub fn compose(gate: GateKind, original_k: u32, g_expr: Box<Expr>, add_coeff: u64) -> Box<Expr> {
    let var_k = Expr::variable(original_k);
    match gate {
        GateKind::And => Expr::and(var_k, g_expr),
        GateKind::Or => Expr::or(var_k, g_expr),
        GateKind::Xor => Expr::xor(var_k, g_expr),
        GateKind::Mul => Expr::mul(var_k, g_expr),
        GateKind::Add => {
            let var_term = if add_coeff == 1 {
                var_k
            } else {
                Expr::mul(Expr::constant(add_coeff), var_k)
            };
            Expr::add(var_term, g_expr)
        }
    }
}

fn is_boolean_valued(sig: &[u64]) -> bool {
    sig.iter().all(|&v| v <= 1)
}

/// Enumerate cofactor-based decomposition candidates across all
/// variables and gate types.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn enumerate_bitwise_candidates(sig: &[u64], num_vars: u32) -> Vec<BitwiseSplitCandidate> {
    let half = sig.len() / 2;
    let mut candidates: Vec<BitwiseSplitCandidate> = Vec::new();
    let mut cof0: Vec<u64> = Vec::with_capacity(half);
    let mut cof1: Vec<u64> = Vec::with_capacity(half);

    for k in 0..num_vars {
        cof0.clear();
        cof1.clear();
        for j in 0..sig.len() {
            if ((j >> k) & 1) == 0 {
                cof0.push(sig[j]);
                cof1.push(sig[j | (1usize << k)]);
            }
        }

        let all_cof0_zero = cof0.iter().all(|&v| v == 0);
        if all_cof0_zero {
            let ng = num_vars - 1;
            let ac = count_active(&cof1, ng);
            if is_boolean_valued(&cof1) {
                candidates.push(BitwiseSplitCandidate {
                    var_k: k,
                    gate: GateKind::And,
                    g_sig: cof1.clone(),
                    add_coeff: 0,
                    active_count: ac,
                });
            }
            candidates.push(BitwiseSplitCandidate {
                var_k: k,
                gate: GateKind::Mul,
                g_sig: cof1.clone(),
                add_coeff: 0,
                active_count: ac,
            });
        }

        let or_match = cof0.iter().zip(cof1.iter()).all(|(&a, &b)| b == (a | 1));
        if or_match {
            let ng = num_vars - 1;
            let ac = count_active(&cof0, ng);
            candidates.push(BitwiseSplitCandidate {
                var_k: k,
                gate: GateKind::Or,
                g_sig: cof0.clone(),
                add_coeff: 0,
                active_count: ac,
            });
        }

        let xor_match = cof0.iter().zip(cof1.iter()).all(|(&a, &b)| b == (a ^ 1));
        if xor_match {
            let ng = num_vars - 1;
            let ac = count_active(&cof0, ng);
            candidates.push(BitwiseSplitCandidate {
                var_k: k,
                gate: GateKind::Xor,
                g_sig: cof0.clone(),
                add_coeff: 0,
                active_count: ac,
            });
        }

        if !all_cof0_zero && !cof0.is_empty() {
            let diff = cof1[0].wrapping_sub(cof0[0]);
            if diff != 0 {
                let add_match = cof0
                    .iter()
                    .zip(cof1.iter())
                    .all(|(&a, &b)| b.wrapping_sub(a) == diff);
                if add_match {
                    let ng = num_vars - 1;
                    let ac = count_active(&cof0, ng);
                    candidates.push(BitwiseSplitCandidate {
                        var_k: k,
                        gate: GateKind::Add,
                        g_sig: cof0.clone(),
                        add_coeff: diff,
                        active_count: ac,
                    });
                }
            }
        }
    }

    candidates.sort_by_key(|c| c.active_count);
    candidates
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn and_match_when_cof0_is_zero() {
        // sig = x & y Boolean-packed: [0, 0, 0, 1]. Cofactor on var 1
        // gives cof0=[0,0], cof1=[0,1] — triggers AND match (cof1 is
        // Boolean).
        let sig = vec![0u64, 0, 0, 1];
        let cands = enumerate_bitwise_candidates(&sig, 2);
        assert!(cands.iter().any(|c| matches!(c.gate, GateKind::And)));
    }

    #[test]
    fn or_match_triggers_for_or_signature() {
        // x | y: [0, 1, 1, 1]. On var 1: cof0=[0,1], cof1=[1,1]. cof1 ==
        // cof0 | 1. So an OR match fires.
        let sig = vec![0u64, 1, 1, 1];
        let cands = enumerate_bitwise_candidates(&sig, 2);
        assert!(cands.iter().any(|c| matches!(c.gate, GateKind::Or)));
    }

    #[test]
    fn compact_signature_drops_dead_vars() {
        // f = x (only var 0 is active even though num_vars=2).
        let sig = vec![0u64, 1, 0, 1];
        let (compact, active) = compact_signature(&sig, 2);
        assert_eq!(compact, vec![0, 1]);
        assert_eq!(active, vec![0]);
    }

    #[test]
    fn remap_vars_rewrites_indices() {
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        let remapped = remap_vars(&e, &[2, 5]);
        let Kind::Add = remapped.kind else {
            panic!("expected Add")
        };
        match (&remapped.children[0].kind, &remapped.children[1].kind) {
            (Kind::Variable(a), Kind::Variable(b)) => {
                assert_eq!(*a, 2);
                assert_eq!(*b, 5);
            }
            _ => panic!("expected Variable children"),
        }
    }
}
