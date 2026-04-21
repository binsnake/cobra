//! Gate kernels operating on 16-lane `u64` probe arrays.
//!
//! `simd` feature backed by the `wide` crate.
//!
//! Every kernel takes inputs pre-masked or applies the supplied mask as
//! appropriate. The scalar and SIMD paths produce byte-for-byte identical

#![forbid(unsafe_code)]

/// constant `kNProbes`. Fixed at 16 so the array size can be materialised
/// as a `u64x8 × 2` split.
pub const N_PROBES: usize = 16;

/// 16-lane probe vector. Simple transparent wrapper so that future
/// place.
pub type ProbeVals = [u64; N_PROBES];

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Gate {
    And,
    Or,
    Xor,
    Add,
    Mul,
}

// ---------- Scalar baseline ----------
//
// to silence dead-code warnings when the `simd` feature supplies the
// public API.

#[allow(dead_code)]
fn gate_apply_scalar(a: &ProbeVals, b: &ProbeVals, g: Gate, mask: u64) -> ProbeVals {
    let mut r: ProbeVals = [0; N_PROBES];
    for i in 0..N_PROBES {
        r[i] = match g {
            Gate::And => a[i] & b[i],
            Gate::Or => a[i] | b[i],
            Gate::Xor => a[i] ^ b[i],
            Gate::Add => a[i].wrapping_add(b[i]) & mask,
            Gate::Mul => a[i].wrapping_mul(b[i]) & mask,
        };
    }
    r
}

#[allow(dead_code)]
fn gate_matches_scalar(
    a: &ProbeVals,
    b: &ProbeVals,
    target: &ProbeVals,
    g: Gate,
    mask: u64,
) -> bool {
    // Accumulate `result_i XOR target_i` into `acc` via OR. `acc == 0` iff
    let applied = gate_apply_scalar(a, b, g, mask);
    let mut acc: u64 = 0;
    for i in 0..N_PROBES {
        acc |= applied[i] ^ target[i];
    }
    acc == 0
}

fn gate_residual_scalar(target: &ProbeVals, a: &ProbeVals, g: Gate, mask: u64) -> ProbeVals {
    let mut r: ProbeVals = [0; N_PROBES];
    match g {
        Gate::Xor => {
            for i in 0..N_PROBES {
                r[i] = target[i] ^ a[i];
            }
        }
        Gate::Add => {
            for i in 0..N_PROBES {
                r[i] = target[i].wrapping_sub(a[i]) & mask;
            }
        }
        // `And`, `Or`, `Mul` are not invertible lane-wise; the C++ version
        // returns a zero-filled `ProbeVals` for those.
        Gate::And | Gate::Or | Gate::Mul => {}
    }
    r
}

// ---------- wide-backed SIMD path ----------

#[cfg(feature = "simd")]
mod simd_impl {
    use wide::u64x4;

    use super::{Gate, ProbeVals, N_PROBES};

    fn load(vals: &ProbeVals, i: usize) -> u64x4 {
        u64x4::new([vals[i], vals[i + 1], vals[i + 2], vals[i + 3]])
    }

    fn store(v: u64x4, out: &mut ProbeVals, i: usize) {
        let arr = v.to_array();
        out[i] = arr[0];
        out[i + 1] = arr[1];
        out[i + 2] = arr[2];
        out[i + 3] = arr[3];
    }

    pub(super) fn gate_apply(a: &ProbeVals, b: &ProbeVals, g: Gate, mask: u64) -> ProbeVals {
        let mut r: ProbeVals = [0; N_PROBES];
        let vm = u64x4::splat(mask);
        for i in (0..N_PROBES).step_by(4) {
            let va = load(a, i);
            let vb = load(b, i);
            let vr = match g {
                Gate::And => va & vb,
                Gate::Or => va | vb,
                Gate::Xor => va ^ vb,
                Gate::Add => (va + vb) & vm,
                Gate::Mul => (va * vb) & vm,
            };
            store(vr, &mut r, i);
        }
        r
    }

    pub(super) fn gate_matches(
        a: &ProbeVals,
        b: &ProbeVals,
        target: &ProbeVals,
        g: Gate,
        mask: u64,
    ) -> bool {
        let vm = u64x4::splat(mask);
        let mut acc = u64x4::ZERO;
        for i in (0..N_PROBES).step_by(4) {
            let va = load(a, i);
            let vb = load(b, i);
            let vt = load(target, i);
            let vr = match g {
                Gate::And => va & vb,
                Gate::Or => va | vb,
                Gate::Xor => va ^ vb,
                Gate::Add => (va + vb) & vm,
                Gate::Mul => (va * vb) & vm,
            };
            acc |= vr ^ vt;
        }
        acc == u64x4::ZERO
    }
}

// ---------- public API (routes scalar vs SIMD based on feature) ----------

/// Apply a gate element-wise across all 16 probe lanes.
#[must_use]
pub fn gate_apply(a: &ProbeVals, b: &ProbeVals, g: Gate, mask: u64) -> ProbeVals {
    #[cfg(feature = "simd")]
    {
        simd_impl::gate_apply(a, b, g, mask)
    }
    #[cfg(not(feature = "simd"))]
    {
        gate_apply_scalar(a, b, g, mask)
    }
}

#[inline]
#[must_use]
pub fn probe0_matches(a0: u64, b0: u64, t0: u64, g: Gate, mask: u64) -> bool {
    match g {
        Gate::And => (a0 & b0) == t0,
        Gate::Or => (a0 | b0) == t0,
        Gate::Xor => (a0 ^ b0) == t0,
        Gate::Add => (a0.wrapping_add(b0) & mask) == t0,
        Gate::Mul => (a0.wrapping_mul(b0) & mask) == t0,
    }
}

/// Check `g(a, b) == target` across all 16 probes.
#[must_use]
pub fn gate_matches(a: &ProbeVals, b: &ProbeVals, target: &ProbeVals, g: Gate, mask: u64) -> bool {
    #[cfg(feature = "simd")]
    {
        simd_impl::gate_matches(a, b, target, g, mask)
    }
    #[cfg(not(feature = "simd"))]
    {
        gate_matches_scalar(a, b, target, g, mask)
    }
}

/// Residual for invertible gates (`Xor`, `Add`); returns zeros otherwise.
#[must_use]
pub fn gate_residual(target: &ProbeVals, a: &ProbeVals, g: Gate, mask: u64) -> ProbeVals {
    gate_residual_scalar(target, a, g, mask)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_probes() -> (ProbeVals, ProbeVals, ProbeVals) {
        let mut a: ProbeVals = [0; N_PROBES];
        let mut b: ProbeVals = [0; N_PROBES];
        let mut t: ProbeVals = [0; N_PROBES];
        for i in 0..N_PROBES {
            // Deterministic pseudo-random-ish inputs.
            a[i] = 0x1234_5678_9ABC_DEF0u64.wrapping_mul(i as u64 + 1);
            b[i] = 0x0BAD_F00D_CAFE_BABEu64.wrapping_mul(i as u64 + 3);
            t[i] = a[i] ^ b[i];
        }
        (a, b, t)
    }

    #[test]
    fn gate_apply_xor_matches_reference() {
        let (a, b, t) = sample_probes();
        let out = gate_apply(&a, &b, Gate::Xor, u64::MAX);
        assert_eq!(out, t);
    }

    #[test]
    fn gate_apply_and_or_xor_match_scalar_at_many_widths() {
        let (a, b, _) = sample_probes();
        for &mask in &[0xFFu64, 0xFFFF, 0xFFFF_FFFF, u64::MAX] {
            for g in [Gate::And, Gate::Or, Gate::Xor, Gate::Add, Gate::Mul] {
                let fast = gate_apply(&a, &b, g, mask);
                let slow = gate_apply_scalar(&a, &b, g, mask);
                assert_eq!(fast, slow, "mismatch on g={g:?} mask={mask:#x}");
            }
        }
    }

    #[test]
    fn gate_matches_true_for_xor_target() {
        let (a, b, t) = sample_probes();
        assert!(gate_matches(&a, &b, &t, Gate::Xor, u64::MAX));
        // AND target for the same inputs is almost certainly not equal to t
        assert!(!gate_matches(&a, &b, &t, Gate::And, u64::MAX));
    }

    #[test]
    fn gate_matches_full_vs_scalar_parity() {
        let (a, b, t) = sample_probes();
        for &mask in &[0xFFu64, 0xFFFFu64, 0xFFFF_FFFF_FFFF_FFFFu64] {
            for g in [Gate::And, Gate::Or, Gate::Xor, Gate::Add, Gate::Mul] {
                let fast = gate_matches(&a, &b, &t, g, mask);
                let slow = gate_matches_scalar(&a, &b, &t, g, mask);
                assert_eq!(fast, slow, "g={g:?} mask={mask:#x}");
            }
        }
    }

    #[test]
    fn probe0_matches_covers_all_gates() {
        assert!(probe0_matches(0xFF, 0x0F, 0x0F, Gate::And, u64::MAX));
        assert!(probe0_matches(0xF0, 0x0F, 0xFF, Gate::Or, u64::MAX));
        assert!(probe0_matches(0xFF, 0x0F, 0xF0, Gate::Xor, u64::MAX));
        assert!(probe0_matches(3, 4, 7, Gate::Add, u64::MAX));
        assert!(probe0_matches(5, 6, 30, Gate::Mul, u64::MAX));

        // Mask
        assert!(probe0_matches(0xFF, 0x01, 0x00, Gate::Add, 0xFF));
    }

    #[test]
    fn gate_residual_xor_recovers_b() {
        let (a, b, _) = sample_probes();
        let t = gate_apply(&a, &b, Gate::Xor, u64::MAX);
        let b_recovered = gate_residual(&t, &a, Gate::Xor, u64::MAX);
        assert_eq!(b_recovered, b);
    }

    #[test]
    fn gate_residual_add_recovers_b_under_mask() {
        let (a, b, _) = sample_probes();
        let mask = 0xFFFFu64;
        let mut a_m = a;
        let mut b_m = b;
        for i in 0..N_PROBES {
            a_m[i] &= mask;
            b_m[i] &= mask;
        }
        let t = gate_apply(&a_m, &b_m, Gate::Add, mask);
        let b_recovered = gate_residual(&t, &a_m, Gate::Add, mask);
        assert_eq!(b_recovered, b_m);
    }

    #[test]
    fn gate_residual_non_invertible_returns_zeros() {
        let (a, _, t) = sample_probes();
        for g in [Gate::And, Gate::Or, Gate::Mul] {
            let out = gate_residual(&t, &a, g, u64::MAX);
            assert!(out.iter().all(|&v| v == 0), "g={g:?}");
        }
    }
}
