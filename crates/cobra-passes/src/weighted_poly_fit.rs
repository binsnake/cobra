//! Weighted falling-factorial coefficient solve — 2-adic Gaussian
//! elimination over `Z/2^n`.
//!
//! Recovers `h_e` such that
//!     `target(x) = Σ h_e · weight(x) · φ_e(x)   (mod 2^bw)`
//! on the `{0..=grid_degree}^k` interpolation grid, where the basis
//! functions are falling factorials and the unknowns are restricted to
//! total degree `≤ max_degree`.
//!
//! The pivot strategy picks the column entry with the lowest 2-adic
//! valuation (smallest `countr_zero`) so the back-substitution can lift
//! through `Z/2^bw` without losing precision.

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};

use cobra_ir::math_utils::{mod_inverse_odd, twos_in_factorial};
use cobra_ir::poly::NormalizedPoly;
use cobra_ir::{MonomialKey, MAX_POLY_VARS};

/// active bitwidth.
pub type WeightFn<'a> = Box<dyn Fn(&[u64], u32) -> u64 + 'a>;

#[derive(Clone, Debug)]
pub struct WeightedFitResult {
    pub poly: NormalizedPoly,
    pub degree_used: u8,
}

mod subcode {
    pub const NO_SUPPORT_VARS: u16 = 12;
    pub const TOO_MANY_VARS: u16 = 10;
    pub const BITWIDTH_RANGE: u16 = 11;
    pub const FIT_FAILED: u16 = 5;
}

fn guard(msg: &'static str, sub: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::GuardFailed,
                domain: ReasonDomain::WeightedPolyFit,
                subcode: sub,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn search_exhausted(msg: &'static str, sub: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::SearchExhausted,
                domain: ReasonDomain::WeightedPolyFit,
                subcode: sub,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

fn falling_factorial(x: u64, n: u8, mask: u64) -> u64 {
    let mut result: u64 = 1;
    for i in 0..u64::from(n) {
        result = result.wrapping_mul(x.wrapping_sub(i)) & mask;
    }
    result
}

fn enumerate_basis_recurse(
    dim: usize,
    remaining: u32,
    per_var_cap: u8,
    cur: &mut Vec<u8>,
    out: &mut Vec<Vec<u8>>,
) {
    if dim == cur.len() {
        out.push(cur.clone());
        return;
    }
    let lim = u32::from(per_var_cap).min(remaining);
    for e in 0..=lim {
        cur[dim] = e as u8;
        enumerate_basis_recurse(dim + 1, remaining - e, per_var_cap, cur, out);
    }
}

/// stable-sort key.
fn enumerate_basis(num_vars: u32, max_degree: u8, per_var_cap: u8) -> Vec<Vec<u8>> {
    let mut basis: Vec<Vec<u8>> = Vec::new();
    let mut cur = vec![0u8; num_vars as usize];
    enumerate_basis_recurse(0, u32::from(max_degree), per_var_cap, &mut cur, &mut basis);

    basis.sort_by(|a, b| {
        let da: u32 = a.iter().map(|&e| u32::from(e)).sum();
        let db: u32 = b.iter().map(|&e| u32::from(e)).sum();
        da.cmp(&db).then_with(|| a.cmp(b))
    });
    basis
}

/// Forward elimination with low-2-adic-valuation pivot selection,
/// rank check, and back-substitution. Returns the solved coefficient
/// vector, or `None` if rank-deficient or inconsistent.
#[allow(clippy::too_many_lines, clippy::needless_range_loop)]
pub(crate) fn solve_2adic(
    mat: &mut [u64],
    rhs: &mut [u64],
    num_cols: usize,
    mask: u64,
    bitwidth: u32,
) -> Option<Vec<u64>> {
    debug_assert!(num_cols > 0);
    debug_assert_eq!(mat.len() % num_cols, 0);
    let num_rows = mat.len() / num_cols;
    debug_assert_eq!(rhs.len(), num_rows);

    let mut is_pivot = vec![false; num_rows];
    let mut pivot_row = vec![0usize; num_cols];
    let mut has_pivot = vec![false; num_cols];

    for col in 0..num_cols {
        let mut best_row = num_rows;
        let mut best_v2 = bitwidth + 1;
        for j in 0..num_rows {
            let v = mat[j * num_cols + col];
            if is_pivot[j] || v == 0 {
                continue;
            }
            let v2 = v.trailing_zeros();
            if v2 < best_v2 {
                best_v2 = v2;
                best_row = j;
            }
        }
        if best_row == num_rows {
            continue;
        }

        is_pivot[best_row] = true;
        has_pivot[col] = true;
        pivot_row[col] = best_row;

        if best_v2 >= bitwidth {
            continue;
        }
        let prec = bitwidth - best_v2;
        let prec_mask = bitmask(prec);
        let piv_inv = mod_inverse_odd(mat[best_row * num_cols + col] >> best_v2, prec);
        let piv_base = best_row * num_cols;

        for i in 0..num_rows {
            if i == best_row {
                continue;
            }
            let row_base = i * num_cols;
            let pivot_col_val = mat[row_base + col];
            if is_pivot[i] || pivot_col_val == 0 {
                continue;
            }
            let mult = ((pivot_col_val >> best_v2).wrapping_mul(piv_inv)) & prec_mask;
            // Split borrows: piv_base != row_base since i != best_row.
            for c in 0..num_cols {
                let term = mult.wrapping_mul(mat[piv_base + c]);
                mat[row_base + c] = mat[row_base + c].wrapping_sub(term) & mask;
            }
            rhs[i] = rhs[i].wrapping_sub(mult.wrapping_mul(rhs[best_row])) & mask;
        }
    }

    for col in 0..num_cols {
        if !has_pivot[col] {
            return None;
        }
    }
    for i in 0..num_rows {
        if !is_pivot[i] && rhs[i] != 0 {
            return None;
        }
    }

    let mut h_raw = vec![0u64; num_cols];
    for col_idx in (0..num_cols).rev() {
        let row = pivot_row[col_idx];
        let row_base = row * num_cols;
        let mut adj_rhs = rhs[row];
        for c in (col_idx + 1)..num_cols {
            adj_rhs = adj_rhs.wrapping_sub(h_raw[c].wrapping_mul(mat[row_base + c])) & mask;
        }
        let pivot_val = mat[row_base + col_idx];
        if pivot_val == 0 {
            return None;
        }
        let t = pivot_val.trailing_zeros();
        if t >= bitwidth {
            h_raw[col_idx] = 0;
            continue;
        }
        if t > 0 && (adj_rhs & ((1u64 << t) - 1)) != 0 {
            return None;
        }
        let prec = bitwidth - t;
        let prec_mask = bitmask(prec);
        let piv_inv = mod_inverse_odd(pivot_val >> t, prec);
        h_raw[col_idx] = ((adj_rhs >> t).wrapping_mul(piv_inv)) & prec_mask;
    }

    Some(h_raw)
}

/// Stack-allocated square-matrix specialization of [`solve_2adic`]. Mirrors
/// the same algorithm but operates on `[[u64; N]; N]` and `[u64; N]`, avoiding
/// heap allocation in hot pattern-matching loops where `N` is small and fixed
/// (e.g. the 4×4 two-var basis-triple system).
#[allow(clippy::needless_range_loop)]
pub(crate) fn solve_2adic_fixed<const N: usize>(
    mat: &mut [[u64; N]; N],
    rhs: &mut [u64; N],
    mask: u64,
    bitwidth: u32,
) -> Option<[u64; N]> {
    let mut is_pivot = [false; N];
    let mut pivot_row = [0usize; N];
    let mut has_pivot = [false; N];

    for col in 0..N {
        let mut best_row = N;
        let mut best_v2 = bitwidth + 1;
        for j in 0..N {
            if is_pivot[j] || mat[j][col] == 0 {
                continue;
            }
            let v2 = mat[j][col].trailing_zeros();
            if v2 < best_v2 {
                best_v2 = v2;
                best_row = j;
            }
        }
        if best_row == N {
            continue;
        }

        is_pivot[best_row] = true;
        has_pivot[col] = true;
        pivot_row[col] = best_row;

        if best_v2 >= bitwidth {
            continue;
        }
        let prec = bitwidth - best_v2;
        let prec_mask = bitmask(prec);
        let piv_inv = mod_inverse_odd(mat[best_row][col] >> best_v2, prec);

        for i in 0..N {
            if is_pivot[i] || mat[i][col] == 0 {
                continue;
            }
            let mult = ((mat[i][col] >> best_v2).wrapping_mul(piv_inv)) & prec_mask;
            for c in 0..N {
                let term = mult.wrapping_mul(mat[best_row][c]);
                mat[i][c] = mat[i][c].wrapping_sub(term) & mask;
            }
            rhs[i] = rhs[i].wrapping_sub(mult.wrapping_mul(rhs[best_row])) & mask;
        }
    }

    for col in 0..N {
        if !has_pivot[col] {
            return None;
        }
    }
    for i in 0..N {
        if !is_pivot[i] && rhs[i] != 0 {
            return None;
        }
    }

    let mut h_raw = [0u64; N];
    for col_idx in (0..N).rev() {
        let row = pivot_row[col_idx];
        let mut adj_rhs = rhs[row];
        for c in (col_idx + 1)..N {
            adj_rhs = adj_rhs.wrapping_sub(h_raw[c].wrapping_mul(mat[row][c])) & mask;
        }
        if mat[row][col_idx] == 0 {
            return None;
        }
        let t = mat[row][col_idx].trailing_zeros();
        if t >= bitwidth {
            h_raw[col_idx] = 0;
            continue;
        }
        if t > 0 && (adj_rhs & ((1u64 << t) - 1)) != 0 {
            return None;
        }
        let prec = bitwidth - t;
        let prec_mask = bitmask(prec);
        let piv_inv = mod_inverse_odd(mat[row][col_idx] >> t, prec);
        h_raw[col_idx] = ((adj_rhs >> t).wrapping_mul(piv_inv)) & prec_mask;
    }

    Some(h_raw)
}

#[allow(clippy::needless_range_loop)]
fn try_solve(
    target: &Evaluator,
    weight: &WeightFn<'_>,
    support_vars: &[u32],
    total_num_vars: u32,
    bitwidth: u32,
    max_degree: u8,
    grid_deg: u8,
) -> Option<WeightedFitResult> {
    let k = support_vars.len() as u32;
    let mask = bitmask(bitwidth);
    let per_var_cap = max_degree.min(grid_deg);

    let basis_exps = enumerate_basis(k, max_degree, per_var_cap);
    let num_cols = basis_exps.len();

    let grid_base = usize::from(grid_deg) + 1;
    let mut num_rows: usize = 1;
    for _ in 0..k {
        num_rows = num_rows.checked_mul(grid_base)?;
    }

    let mut mat: Vec<u64> = vec![0u64; num_rows * num_cols];
    let mut rhs: Vec<u64> = vec![0u64; num_rows];
    let mut full_point: Vec<u64> = vec![0u64; total_num_vars as usize];
    let mut local_point: Vec<u64> = vec![0u64; k as usize];

    // Precompute falling_factorial(coord, degree, mask) indexed by [axis][coord][degree].
    // axis: 0..k, coord: 0..grid_base, degree: 0..=per_var_cap.
    let deg_dim = usize::from(per_var_cap) + 1;
    let mut ff_table: Vec<u64> = vec![0u64; (k as usize) * grid_base * deg_dim];
    for axis in 0..k as usize {
        for coord in 0..grid_base {
            for deg in 0..deg_dim {
                ff_table[(axis * grid_base + coord) * deg_dim + deg] =
                    falling_factorial(coord as u64, deg as u8, mask);
            }
        }
    }

    for row in 0..num_rows {
        let mut tmp = row;
        for i in 0..k as usize {
            let coord = (tmp % grid_base) as u64;
            local_point[i] = coord;
            full_point[support_vars[i] as usize] = coord;
            tmp /= grid_base;
        }
        rhs[row] = target.eval(&full_point) & mask;
        let w_val = weight(&local_point, bitwidth);
        for col in 0..num_cols {
            let mut phi: u64 = 1;
            for i in 0..k as usize {
                let coord = local_point[i] as usize;
                let deg = basis_exps[col][i] as usize;
                phi = phi.wrapping_mul(ff_table[(i * grid_base + coord) * deg_dim + deg]) & mask;
            }
            mat[row * num_cols + col] = w_val.wrapping_mul(phi) & mask;
        }
        for &idx in support_vars {
            full_point[idx as usize] = 0;
        }
    }

    let h_raw = solve_2adic(&mut mat, &mut rhs, num_cols, mask, bitwidth)?;

    let nv = total_num_vars as u8;
    let mut poly = NormalizedPoly::empty(nv, bitwidth);
    let mut degree_used: u8 = 0;
    let mut exps = [0u8; MAX_POLY_VARS];

    for col in 0..num_cols {
        let mut h = h_raw[col] & mask;
        if h == 0 {
            continue;
        }
        exps.fill(0);
        let mut total_deg: u32 = 0;
        for i in 0..k as usize {
            exps[support_vars[i] as usize] = basis_exps[col][i];
            total_deg += u32::from(basis_exps[col][i]);
        }
        let q: u32 = (0..k as usize)
            .map(|i| twos_in_factorial(u32::from(basis_exps[col][i])))
            .sum();
        if q >= bitwidth {
            continue;
        }
        if q > 0 {
            h &= bitmask(bitwidth - q);
        }
        if h == 0 {
            continue;
        }
        let key = MonomialKey::from_exponents(&exps, nv);
        poly.coeffs.insert(key, h);
        if total_deg > u32::from(degree_used) {
            degree_used = total_deg as u8;
        }
    }

    Some(WeightedFitResult { poly, degree_used })
}

pub fn recover_weighted_poly(
    target: &Evaluator,
    weight: &WeightFn<'_>,
    support_vars: &[u32],
    total_num_vars: u32,
    bitwidth: u32,
    max_degree: u8,
    grid_degree: u8,
) -> SolverResult<WeightedFitResult> {
    if support_vars.is_empty() {
        return SolverResult::Inapplicable(guard(
            "empty support variable set",
            subcode::NO_SUPPORT_VARS,
        ));
    }
    if total_num_vars as usize > MAX_POLY_VARS {
        return SolverResult::Inapplicable(guard(
            "total_num_vars exceeds MAX_POLY_VARS",
            subcode::TOO_MANY_VARS,
        ));
    }
    if !(2..=64).contains(&bitwidth) {
        return SolverResult::Inapplicable(guard(
            "bitwidth out of range [2, 64]",
            subcode::BITWIDTH_RANGE,
        ));
    }
    for &idx in support_vars {
        if idx >= total_num_vars {
            return SolverResult::Inapplicable(guard(
                "support index exceeds total_num_vars",
                subcode::NO_SUPPORT_VARS,
            ));
        }
    }

    match try_solve(
        target,
        weight,
        support_vars,
        total_num_vars,
        bitwidth,
        max_degree,
        grid_degree,
    ) {
        Some(fit) => SolverResult::Success(fit),
        None => SolverResult::Blocked(search_exhausted("2-adic solve failed", subcode::FIT_FAILED)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::arith::bitmask;

    fn weight_one() -> WeightFn<'static> {
        Box::new(|_pt: &[u64], _bw: u32| 1u64)
    }

    #[test]
    fn enumerate_basis_orders_by_total_degree() {
        let basis = enumerate_basis(2, 2, 2);
        // Expected degree 0, then 1s, then 2s. Lex within each group.
        assert_eq!(basis[0], vec![0, 0]);
        assert_eq!(basis[1], vec![0, 1]);
        assert_eq!(basis[2], vec![1, 0]);
        // Total-degree-2 entries
        let deg2: Vec<&Vec<u8>> = basis
            .iter()
            .filter(|e| e.iter().map(|&x| u32::from(x)).sum::<u32>() == 2)
            .collect();
        assert_eq!(deg2.len(), 3); // (0,2), (1,1), (2,0)
    }

    #[test]
    fn falling_factorial_matches_definition() {
        let mask = bitmask(64);
        // x*(x-1)*(x-2) at x=5 → 5*4*3 = 60
        assert_eq!(falling_factorial(5, 3, mask), 60);
        // 0! = 1
        assert_eq!(falling_factorial(7, 0, mask), 1);
    }

    #[test]
    fn recovers_constant_polynomial_with_unit_weight() {
        // target(x) = 7 for all x, weight ≡ 1, k = 1.
        let target = Evaluator::from_closure(|_vals: &[u64]| 7u64);
        let w = weight_one();
        let result = recover_weighted_poly(&target, &w, &[0], 1, 64, 0, 1);
        let SolverResult::Success(fit) = result else {
            panic!("expected success, got {result:?}");
        };
        assert_eq!(fit.degree_used, 0);
        // Single monomial: the constant 7.
        let zero = MonomialKey::zero();
        assert_eq!(fit.poly.coeffs.get(&zero).copied(), Some(7));
    }

    #[test]
    fn recovers_linear_polynomial() {
        // target(x) = 3*x + 5, weight ≡ 1, k = 1, bitwidth 64.
        let target =
            Evaluator::from_closure(|vals: &[u64]| 3u64.wrapping_mul(vals[0]).wrapping_add(5));
        let w = weight_one();
        let result = recover_weighted_poly(&target, &w, &[0], 1, 64, 1, 2);
        let SolverResult::Success(fit) = result else {
            panic!("expected success, got {result:?}");
        };
        assert_eq!(fit.degree_used, 1);
        let zero = MonomialKey::zero();
        let x1 = MonomialKey::zero().with_exponent(0, 1);
        // Constant term is 5, linear term is 3 (falling-factorial basis is the
        // identity for degree-1 in one variable).
        assert_eq!(fit.poly.coeffs.get(&zero).copied(), Some(5));
        assert_eq!(fit.poly.coeffs.get(&x1).copied(), Some(3));
    }

    #[test]
    fn recovers_two_var_quadratic() {
        // target(x, y) = 2*x*y + x + 3 (mod 2^64), weight ≡ 1.
        // In falling-factorial basis the same polynomial reads as
        //   2 * x^(1) * y^(1) + 1 * x^(1) + 3 * 1
        // because falling factorials of degree ≤ 1 coincide with monomials.
        let target = Evaluator::from_closure(|vals: &[u64]| {
            2u64.wrapping_mul(vals[0])
                .wrapping_mul(vals[1])
                .wrapping_add(vals[0])
                .wrapping_add(3)
        });
        let w = weight_one();
        let result = recover_weighted_poly(&target, &w, &[0, 1], 2, 64, 2, 2);
        let SolverResult::Success(fit) = result else {
            panic!("expected success, got {result:?}");
        };
        assert_eq!(fit.degree_used, 2);
        let zero = MonomialKey::zero();
        let x1 = MonomialKey::zero().with_exponent(0, 1);
        let xy = MonomialKey::zero().with_exponent(0, 1).with_exponent(1, 1);
        assert_eq!(fit.poly.coeffs.get(&zero).copied(), Some(3));
        assert_eq!(fit.poly.coeffs.get(&x1).copied(), Some(1));
        assert_eq!(fit.poly.coeffs.get(&xy).copied(), Some(2));
    }

    #[test]
    fn even_weight_loses_low_bits() {
        // target(x) = 2*x, weight(x) = 2 — every row carries one factor of 2.
        // The recovered coefficient must reflect that lost precision: the only
        // monomial is x with coefficient 1, valid modulo 2^(bw-1).
        let target = Evaluator::from_closure(|vals: &[u64]| 2u64.wrapping_mul(vals[0]));
        let w: WeightFn<'static> = Box::new(|_pt: &[u64], _bw: u32| 2u64);
        let result = recover_weighted_poly(&target, &w, &[0], 1, 64, 1, 2);
        let SolverResult::Success(fit) = result else {
            panic!("expected success, got {result:?}");
        };
        let x1 = MonomialKey::zero().with_exponent(0, 1);
        assert_eq!(fit.poly.coeffs.get(&x1).copied(), Some(1));
    }

    #[test]
    fn empty_support_is_inapplicable() {
        let target = Evaluator::from_closure(|_: &[u64]| 0);
        let w = weight_one();
        let r = recover_weighted_poly(&target, &w, &[], 1, 64, 1, 1);
        assert!(matches!(r, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn out_of_range_bitwidth_is_inapplicable() {
        let target = Evaluator::from_closure(|_: &[u64]| 0);
        let w = weight_one();
        let r = recover_weighted_poly(&target, &w, &[0], 1, 1, 1, 1);
        assert!(matches!(r, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn support_index_out_of_bounds_is_inapplicable() {
        let target = Evaluator::from_closure(|_: &[u64]| 0);
        let w = weight_one();
        let r = recover_weighted_poly(&target, &w, &[5], 2, 64, 1, 1);
        assert!(matches!(r, SolverResult::Inapplicable(_)));
    }
}
