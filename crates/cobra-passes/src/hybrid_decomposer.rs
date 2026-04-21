//! Hybrid decomposer: strip an invertible operator (XOR or ADD) on a
//! single variable from the outside, shrinking the residual. The
//! outer composition rewrites `f = x_k OP r(x)` for `OP ∈ {^, +}`.
//! Sorted ascending by `active_count` so the smallest residual wins.

use cobra_core::expr::Expr;

use cobra_orchestrator::ExtractOp;

#[derive(Clone, Debug)]
pub struct HybridExtractionCandidate {
    pub var_k: u32,
    pub op: ExtractOp,
    pub r_sig: Vec<u64>,
    pub active_count: u32,
}

fn count_active_vars(sig: &[u64], n: u32) -> u32 {
    let mut count = 0;
    for v in 0..n {
        for j in 0..sig.len() {
            let flipped = j ^ (1usize << v);
            if sig[j] != sig[flipped] {
                count += 1;
                break;
            }
        }
    }
    count
}

/// Build the residual signature after stripping `op` on variable `k`:
/// `r_sig[i] = sig[i] op^{-1} bit_k(i)`.
#[must_use]
pub fn build_residual_sig(sig: &[u64], k: u32, op: ExtractOp) -> Vec<u64> {
    sig.iter()
        .enumerate()
        .map(|(i, &v)| {
            let vk = (i as u64 >> k) & 1;
            match op {
                ExtractOp::Xor => v ^ vk,
                ExtractOp::Add => v.wrapping_sub(vk),
            }
        })
        .collect()
}

/// Compose `f = x_k OP r_expr`.
#[must_use]
pub fn compose_extraction(op: ExtractOp, original_k: u32, r_expr: Box<Expr>) -> Box<Expr> {
    let var_k = Expr::variable(original_k);
    match op {
        ExtractOp::Xor => Expr::xor(var_k, r_expr),
        ExtractOp::Add => Expr::add(var_k, r_expr),
    }
}

/// Enumerate all single-variable extraction candidates across both
/// operators; sorted ascending by residual active-variable count.
#[must_use]
pub fn enumerate_hybrid_candidates(sig: &[u64], num_vars: u32) -> Vec<HybridExtractionCandidate> {
    let mut candidates: Vec<HybridExtractionCandidate> = Vec::with_capacity(2 * num_vars as usize);
    for k in 0..num_vars {
        for op in [ExtractOp::Xor, ExtractOp::Add] {
            let r_sig = build_residual_sig(sig, k, op);
            if r_sig == sig {
                continue;
            }
            let r_active = count_active_vars(&r_sig, num_vars);
            candidates.push(HybridExtractionCandidate {
                var_k: k,
                op,
                r_sig,
                active_count: r_active,
            });
        }
    }
    candidates.sort_by_key(|c| c.active_count);
    candidates
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xor_extraction_on_bit_0_reduces_active_count() {
        // sig for x ^ y at 2-var Boolean: [0, 1, 1, 0] — stripping XOR on
        // var 0 should yield residual [0, 0, 1, 1] which is just `y`
        // (active_count = 1).
        let sig = vec![0u64, 1, 1, 0];
        let cands = enumerate_hybrid_candidates(&sig, 2);
        assert!(cands
            .iter()
            .any(|c| c.var_k == 0 && matches!(c.op, ExtractOp::Xor) && c.active_count == 1));
    }

    #[test]
    fn build_residual_sig_xor_subtracts_bit_k() {
        let sig = vec![0u64, 1, 1, 0];
        let r = build_residual_sig(&sig, 0, ExtractOp::Xor);
        assert_eq!(r, vec![0, 0, 1, 1]);
    }

    #[test]
    fn compose_extraction_xor_builds_expected_shape() {
        let r = Expr::variable(1);
        let composed = compose_extraction(ExtractOp::Xor, 0, r);
        assert!(matches!(composed.kind, cobra_core::expr::Kind::Xor));
    }
}
