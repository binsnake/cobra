//! Symbolic self-check: normalise `reconstructed` back to a
//! [`SemilinearIR`] and verify it matches `original_ir` coefficient-
//! for-coefficient.
//!
//! Cheaper than a full-width evaluator probe and essential during the
//! semilinear rewrite chain — if a rewrite produces a representation
//! that renormalises to a different coefficient map, it cannot be
//! equivalent to the input.

use cobra_core::arith::bitmask;
use cobra_core::expr::Expr;

use cobra_ir::normalize_to_semilinear;
use cobra_ir::semilinear::{AtomKey, SemilinearIR};

#[derive(Clone, Debug, Default)]
pub struct SelfCheckResult {
    pub passed: bool,
    pub mismatch_detail: String,
}

fn build_coeff_map(ir: &SemilinearIR, mask: u64) -> std::collections::HashMap<AtomKey, u64> {
    let mut result: std::collections::HashMap<AtomKey, u64> = std::collections::HashMap::new();
    for term in &ir.terms {
        let key = ir.atom_table[term.atom_id as usize].key.clone();
        let slot = result.entry(key).or_insert(0);
        *slot = slot.wrapping_add(term.coeff) & mask;
    }
    result.retain(|_, &mut v| v != 0);
    result
}

/// Symbolic self-check of a reconstructed expression against its
/// original [`SemilinearIR`]. Returns a [`SelfCheckResult`] with a
/// human-readable mismatch string on failure.
#[must_use]
pub fn self_check_semilinear(
    original_ir: &SemilinearIR,
    reconstructed: &Expr,
    vars: &[String],
    bitwidth: u32,
) -> SelfCheckResult {
    let re = match normalize_to_semilinear(reconstructed, vars, bitwidth) {
        Ok(ir) => ir,
        Err(e) => {
            return SelfCheckResult {
                passed: false,
                mismatch_detail: format!("re-normalization failed: {}", e.message),
            };
        }
    };
    let mask = bitmask(bitwidth);

    if (original_ir.constant & mask) != (re.constant & mask) {
        return SelfCheckResult {
            passed: false,
            mismatch_detail: format!(
                "constant mismatch: original=0x{:x} re=0x{:x}",
                original_ir.constant & mask,
                re.constant & mask
            ),
        };
    }

    let orig_map = build_coeff_map(original_ir, mask);
    let re_map = build_coeff_map(&re, mask);

    if orig_map.len() != re_map.len() {
        return SelfCheckResult {
            passed: false,
            mismatch_detail: format!(
                "term count mismatch: original={} re={}",
                orig_map.len(),
                re_map.len()
            ),
        };
    }

    for (key, coeff) in &orig_map {
        match re_map.get(key) {
            None => {
                return SelfCheckResult {
                    passed: false,
                    mismatch_detail: "atom present in original but missing in re-normalized".into(),
                };
            }
            Some(re_coeff) if re_coeff != coeff => {
                return SelfCheckResult {
                    passed: false,
                    mismatch_detail: format!(
                        "coefficient mismatch for atom: original=0x{coeff:x} re=0x{re_coeff:x}"
                    ),
                };
            }
            Some(_) => {}
        }
    }

    SelfCheckResult {
        passed: true,
        mismatch_detail: String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_expression_self_checks() {
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        let ir = normalize_to_semilinear(&e, &["x".into(), "y".into()], 64).unwrap();
        let re = Expr::add(Expr::variable(0), Expr::variable(1));
        let r = self_check_semilinear(&ir, &re, &["x".into(), "y".into()], 64);
        assert!(r.passed, "detail: {}", r.mismatch_detail);
    }

    #[test]
    fn different_constant_flags_mismatch() {
        let orig = Expr::add(Expr::variable(0), Expr::constant(5));
        let ir = normalize_to_semilinear(&orig, &["x".into()], 64).unwrap();
        let different = Expr::add(Expr::variable(0), Expr::constant(7));
        let r = self_check_semilinear(&ir, &different, &["x".into()], 64);
        assert!(!r.passed);
        assert!(r.mismatch_detail.contains("constant mismatch"));
    }

    #[test]
    fn different_coefficient_flags_mismatch() {
        let orig = Expr::mul(Expr::constant(3), Expr::variable(0));
        let ir = normalize_to_semilinear(&orig, &["x".into()], 64).unwrap();
        let different = Expr::mul(Expr::constant(5), Expr::variable(0));
        let r = self_check_semilinear(&ir, &different, &["x".into()], 64);
        assert!(!r.passed);
    }

    #[test]
    fn non_semilinear_reconstruction_is_detected() {
        // Original is linear, but the reconstruction contains x*y.
        let orig = Expr::add(Expr::variable(0), Expr::variable(1));
        let ir = normalize_to_semilinear(&orig, &["x".into(), "y".into()], 64).unwrap();
        let bad = Expr::mul(Expr::variable(0), Expr::variable(1));
        let r = self_check_semilinear(&ir, &bad, &["x".into(), "y".into()], 64);
        assert!(!r.passed);
    }
}
