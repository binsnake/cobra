//! Template decomposer — bounded structural search.
//!
//! Tries to express the target function as a small composition of
//! atoms drawn from a precomputed pool (constants, variables, unary
//! ops, pairwise ops, and their negations/NOTs).
//!
//!   Layer 1: `target = G(A, B)`
//!   Layer 2: `target = G_out(A, G_in(B, C))`
//!   Wrap:    `Neg(target)` or `Not(target)` re-checked against L1+L2
//!   Layer 3: `target = G1(A, G2(B, R))`           (G1, G2 invertible)
//!   Layer 4: `target = G1(A, Unary(G2(B, R)))`    (G1 invertible)
//!
//! All candidates are full-width verified through the evaluator before
//! being accepted. Atoms are deduplicated by a fingerprint of their
//! 16-probe value vector; collisions are statistically negligible at
//! these pool sizes.

#![allow(
    clippy::needless_range_loop,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use std::collections::HashMap;

use cobra_core::arith::bitmask;
use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::{compute_cost, is_better, ExprCost};
use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
    VerificationState,
};

use crate::spot_check::{full_width_check_eval, DEFAULT_NUM_SAMPLES};

const N_PROBES: usize = 16;
const MAX_VARS: u32 = 6;

mod subcode {
    pub const NO_EVALUATOR: u16 = 1;
    pub const TOO_MANY_VARS: u16 = 2;
    pub const COST_REJECTED: u16 = 3;
    pub const NO_MATCH: u16 = 10;
}

#[derive(Clone, Debug)]
pub struct TemplateResult {
    pub expr: Box<Expr>,
    pub cost: ExprCost,
    pub verification: VerificationState,
}

#[derive(Copy, Clone)]
enum Gate {
    And,
    Or,
    Xor,
    Add,
    Mul,
}

const ALL_GATES: [Gate; 5] = [Gate::And, Gate::Or, Gate::Xor, Gate::Add, Gate::Mul];

fn gate_invertible(g: Gate) -> bool {
    matches!(g, Gate::Xor | Gate::Add)
}

fn gate_apply(a: u64, b: u64, g: Gate, mask: u64) -> u64 {
    match g {
        Gate::And => a & b,
        Gate::Or => a | b,
        Gate::Xor => a ^ b,
        Gate::Add => a.wrapping_add(b) & mask,
        Gate::Mul => a.wrapping_mul(b) & mask,
    }
}

fn gate_residual(target: u64, a: u64, g: Gate, mask: u64) -> u64 {
    match g {
        Gate::Xor => target ^ a,
        Gate::Add => target.wrapping_sub(a) & mask,
        _ => 0,
    }
}

fn gate_expr(g: Gate, a: Box<Expr>, b: Box<Expr>) -> Box<Expr> {
    match g {
        Gate::And => Expr::and(a, b),
        Gate::Or => Expr::or(a, b),
        Gate::Xor => Expr::xor(a, b),
        Gate::Add => Expr::add(a, b),
        Gate::Mul => Expr::mul(a, b),
    }
}

// ---------------------------------------------------------------
// ProbeVals — fixed-width 16-probe sample of an expression.
// ---------------------------------------------------------------

#[derive(Copy, Clone, Default)]
struct ProbeVals([u64; N_PROBES]);

impl ProbeVals {
    fn fingerprint(&self) -> u64 {
        let mut h: u64 = 0;
        for (i, &v) in self.0.iter().enumerate() {
            h ^= v.wrapping_mul(0x9E37_79B9_7F4A_7C15u64.wrapping_add(i as u64));
        }
        h
    }

    fn apply_gate(&self, other: &Self, g: Gate, mask: u64) -> Self {
        let mut r = Self::default();
        for i in 0..N_PROBES {
            r.0[i] = gate_apply(self.0[i], other.0[i], g, mask);
        }
        r
    }

    fn residual(&self, a: &Self, g: Gate, mask: u64) -> Self {
        let mut r = Self::default();
        for i in 0..N_PROBES {
            r.0[i] = gate_residual(self.0[i], a.0[i], g, mask);
        }
        r
    }

    fn neg(&self, mask: u64) -> Self {
        let mut r = Self::default();
        for i in 0..N_PROBES {
            r.0[i] = self.0[i].wrapping_neg() & mask;
        }
        r
    }

    fn not_op(&self, mask: u64) -> Self {
        let mut r = Self::default();
        for i in 0..N_PROBES {
            r.0[i] = (!self.0[i]) & mask;
        }
        r
    }
}

fn probe(e: &Expr, pts: &[Vec<u64>], bw: u32) -> ProbeVals {
    let eval = Evaluator::from_expr(e, bw);
    let mut v = ProbeVals::default();
    for i in 0..N_PROBES {
        v.0[i] = eval.eval(&pts[i]);
    }
    v
}

// ---------------------------------------------------------------
// Match predicates (scalar; the C++ uses Highway SIMD here).
// ---------------------------------------------------------------

fn probe0_matches(a0: u64, b0: u64, t0: u64, g: Gate, mask: u64) -> bool {
    gate_apply(a0, b0, g, mask) == t0
}

fn gate_matches(a: &ProbeVals, b: &ProbeVals, target: &ProbeVals, g: Gate, mask: u64) -> bool {
    for i in 0..N_PROBES {
        if gate_apply(a.0[i], b.0[i], g, mask) != target.0[i] {
            return false;
        }
    }
    true
}

fn and_matches(a: &ProbeVals, b: &ProbeVals, target: &ProbeVals) -> bool {
    for i in 0..N_PROBES {
        if (a.0[i] & b.0[i]) != target.0[i] {
            return false;
        }
    }
    true
}

fn or_matches(a: &ProbeVals, b: &ProbeVals, target: &ProbeVals) -> bool {
    for i in 0..N_PROBES {
        if (a.0[i] | b.0[i]) != target.0[i] {
            return false;
        }
    }
    true
}

fn mul_matches(
    a: &ProbeVals,
    b: &ProbeVals,
    target: &ProbeVals,
    mask: u64,
    start_probe: usize,
) -> bool {
    for i in start_probe..N_PROBES {
        if (a.0[i].wrapping_mul(b.0[i])) & mask != target.0[i] {
            return false;
        }
    }
    true
}

/// Compatibility guard: rejects atoms that can't be operands of a
/// non-invertible gate producing the target.
///   AND: every target bit must already be set in `a`.
///   OR : every `a` bit must already be set in the target.
fn compatible(a: &ProbeVals, target: &ProbeVals, g: Gate) -> bool {
    match g {
        Gate::And => (0..N_PROBES).all(|i| (target.0[i] & !a.0[i]) == 0),
        Gate::Or => (0..N_PROBES).all(|i| (a.0[i] & !target.0[i]) == 0),
        _ => true,
    }
}

// ---------------------------------------------------------------
// Atom pool.
// ---------------------------------------------------------------

struct Atom {
    expr: Box<Expr>,
    vals: ProbeVals,
    cost: ExprCost,
}

#[derive(Default)]
struct ValMap {
    map: HashMap<u64, u32>,
}

impl ValMap {
    fn insert(&mut self, key: &ProbeVals, value: usize) {
        self.map.entry(key.fingerprint()).or_insert(value as u32);
    }

    fn find(&self, key: &ProbeVals) -> Option<usize> {
        self.map.get(&key.fingerprint()).map(|&v| v as usize)
    }

    fn contains(&self, key: &ProbeVals) -> bool {
        self.map.contains_key(&key.fingerprint())
    }
}

fn push(pool: &mut Vec<Atom>, idx: &mut ValMap, e: Box<Expr>, vals: ProbeVals) {
    let new_cost = compute_cost(&e).cost;
    if let Some(slot) = idx.find(&vals) {
        if is_better(&new_cost, &pool[slot].cost) {
            pool[slot].expr = e;
            pool[slot].cost = new_cost;
        }
        return;
    }
    let slot = pool.len();
    idx.insert(&vals, slot);
    pool.push(Atom {
        expr: e,
        vals,
        cost: new_cost,
    });
}

fn populate(pool: &mut Vec<Atom>, idx: &mut ValMap, nv: u32, pts: &[Vec<u64>], bw: u32) {
    let mask = bitmask(bw);
    let add = |pool: &mut Vec<Atom>, idx: &mut ValMap, e: Box<Expr>| {
        let v = probe(&e, pts, bw);
        push(pool, idx, e, v);
    };

    add(pool, idx, Expr::constant(0));
    add(pool, idx, Expr::constant(1));
    add(pool, idx, Expr::constant(2));
    add(pool, idx, Expr::constant(mask));

    for i in 0..nv {
        add(pool, idx, Expr::variable(i));
        add(pool, idx, Expr::neg(Expr::variable(i)));
        add(pool, idx, Expr::not(Expr::variable(i)));
    }

    for i in 0..nv {
        for j in i..nv {
            add(pool, idx, Expr::and(Expr::variable(i), Expr::variable(j)));
            add(pool, idx, Expr::or(Expr::variable(i), Expr::variable(j)));
            add(pool, idx, Expr::xor(Expr::variable(i), Expr::variable(j)));
            add(pool, idx, Expr::add(Expr::variable(i), Expr::variable(j)));
            add(pool, idx, Expr::mul(Expr::variable(i), Expr::variable(j)));
        }
    }

    for i in 0..nv {
        for j in 0..nv {
            if i == j {
                continue;
            }
            add(
                pool,
                idx,
                Expr::add(Expr::variable(i), Expr::neg(Expr::variable(j))),
            );
        }
    }

    let base = pool.len();
    for k in 0..base {
        let neg_v = pool[k].vals.neg(mask);
        let not_v = pool[k].vals.not_op(mask);
        let neg_e = Expr::neg(pool[k].expr.clone_tree());
        let not_e = Expr::not(pool[k].expr.clone_tree());
        push(pool, idx, neg_e, neg_v);
        push(pool, idx, not_e, not_v);
    }
}

// ---------------------------------------------------------------
// Inner-composition cache.
// ---------------------------------------------------------------

struct InnerComp {
    gate: Gate,
    bi: usize,
    ci: usize,
    vals: ProbeVals,
}

#[derive(Default)]
struct InnerCompositions {
    comps: Vec<InnerComp>,
    index: ValMap,
    mul_probe0_buckets: HashMap<u64, Vec<usize>>,
}

fn build_inner_compositions(pool: &[Atom], vmap: &ValMap, mask: u64) -> InnerCompositions {
    let mut inner = InnerCompositions::default();
    let pn = pool.len();
    for &g_in in &ALL_GATES {
        for bi in 0..pn {
            for ci in bi..pn {
                // Idempotent self-application produces a ProbeVals already in vmap:
                // And(x,x) = Or(x,x) = x; Xor(x,x) = 0 (constant atom); Add(x,x) = 2*x
                // often collides with existing atoms. Skip the trivial same-operand cases
                // for idempotent gates up front to avoid the apply_gate + lookup work.
                if bi == ci && matches!(g_in, Gate::And | Gate::Or) {
                    continue;
                }
                let v = pool[bi].vals.apply_gate(&pool[ci].vals, g_in, mask);
                if vmap.contains(&v) || inner.index.contains(&v) {
                    continue;
                }
                let slot = inner.comps.len();
                inner.index.insert(&v, slot);
                inner
                    .mul_probe0_buckets
                    .entry(v.0[0])
                    .or_default()
                    .push(slot);
                inner.comps.push(InnerComp {
                    gate: g_in,
                    bi,
                    ci,
                    vals: v,
                });
            }
        }
    }
    inner
}

fn make_inner(pool: &[Atom], ic: &InnerComp) -> Box<Expr> {
    gate_expr(
        ic.gate,
        pool[ic.bi].expr.clone_tree(),
        pool[ic.ci].expr.clone_tree(),
    )
}

// ---------------------------------------------------------------
// Mul probe-0 bucket filter (lifts target via 2-adic inverse).
// ---------------------------------------------------------------

fn collect_mul_probe0_candidates(
    buckets: &HashMap<u64, Vec<usize>>,
    lhs_probe0: u64,
    target_probe0: u64,
    bitwidth: u32,
    out: &mut Vec<usize>,
) -> bool {
    const MAX_ENUMERATED_SHIFT: u32 = 8;

    out.clear();
    let bw_mask = bitmask(bitwidth);
    let lhs0 = lhs_probe0 & bw_mask;
    let tgt0 = target_probe0 & bw_mask;

    if lhs0 == 0 {
        return tgt0 != 0;
    }

    let twos = bitwidth.min(lhs0.trailing_zeros());
    let twos_mask = bitmask(twos);
    if (tgt0 & twos_mask) != 0 {
        return true;
    }
    if twos > MAX_ENUMERATED_SHIFT {
        return false;
    }

    let reduced_bits = bitwidth - twos;
    let base_solution: u64 = if reduced_bits > 0 {
        let odd_part = lhs0 >> twos;
        let reduced_target = tgt0 >> twos;
        let inv = cobra_ir::math_utils::mod_inverse_odd(odd_part, reduced_bits);
        (inv.wrapping_mul(reduced_target)) & bitmask(reduced_bits)
    } else {
        0
    };

    let mut append_bucket = |key: u64| {
        if let Some(v) = buckets.get(&key) {
            out.extend_from_slice(v);
        }
    };

    if twos == 0 {
        append_bucket(base_solution & bw_mask);
        return true;
    }

    let step: u64 = 1u64 << reduced_bits;
    let solution_count: u64 = 1u64 << twos;
    for k in 0..solution_count {
        append_bucket(base_solution.wrapping_add(k.wrapping_mul(step)) & bw_mask);
    }
    true
}

// ---------------------------------------------------------------
// Verify and update the running best result.
// ---------------------------------------------------------------

fn try_update(
    best: &mut Option<TemplateResult>,
    candidate: Box<Expr>,
    eval: &Evaluator,
    nv: u32,
    bw: u32,
    baseline: Option<&ExprCost>,
) -> bool {
    let chk = full_width_check_eval(eval, nv, &candidate, bw, DEFAULT_NUM_SAMPLES);
    if !chk.passed {
        return false;
    }
    let info = compute_cost(&candidate);
    if let Some(b) = baseline {
        if !is_better(&info.cost, b) {
            return false;
        }
    }
    if let Some(b) = best {
        if !is_better(&info.cost, &b.cost) {
            return false;
        }
    }
    *best = Some(TemplateResult {
        expr: candidate,
        cost: info.cost,
        verification: VerificationState::Verified,
    });
    true
}

// ---------------------------------------------------------------
// Layer 1: target = G(A, B)
// ---------------------------------------------------------------

fn layer1(
    target: &ProbeVals,
    pool: &[Atom],
    vmap: &ValMap,
    mask: u64,
    eval: &Evaluator,
    nv: u32,
    bw: u32,
    baseline: Option<&ExprCost>,
) -> Option<TemplateResult> {
    let mut best: Option<TemplateResult> = None;
    let pn = pool.len();
    for &g in &ALL_GATES {
        if gate_invertible(g) {
            for ai in 0..pn {
                let res = target.residual(&pool[ai].vals, g, mask);
                let Some(slot) = vmap.find(&res) else {
                    continue;
                };
                let e = gate_expr(g, pool[ai].expr.clone_tree(), pool[slot].expr.clone_tree());
                try_update(&mut best, e, eval, nv, bw, baseline);
            }
        } else {
            for ai in 0..pn {
                for bi in 0..pn {
                    if !probe0_matches(pool[ai].vals.0[0], pool[bi].vals.0[0], target.0[0], g, mask)
                    {
                        continue;
                    }
                    if !gate_matches(&pool[ai].vals, &pool[bi].vals, target, g, mask) {
                        continue;
                    }
                    let e = gate_expr(g, pool[ai].expr.clone_tree(), pool[bi].expr.clone_tree());
                    try_update(&mut best, e, eval, nv, bw, baseline);
                }
            }
        }
        if best.is_some() {
            return best;
        }
    }
    best
}

// ---------------------------------------------------------------
// Layer 2: target = G_out(A, G_in(B, C))
// ---------------------------------------------------------------

fn collect_compatible_atoms(pool: &[Atom], target: &ProbeVals, g: Gate) -> Vec<usize> {
    (0..pool.len())
        .filter(|&i| compatible(&pool[i].vals, target, g))
        .collect()
}

fn collect_compatible_inner(inner: &[InnerComp], target: &ProbeVals, g: Gate) -> Vec<usize> {
    (0..inner.len())
        .filter(|&i| compatible(&inner[i].vals, target, g))
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn layer2(
    target: &ProbeVals,
    pool: &[Atom],
    inner_cache: &InnerCompositions,
    mask: u64,
    eval: &Evaluator,
    nv: u32,
    bw: u32,
    baseline: Option<&ExprCost>,
) -> Option<TemplateResult> {
    let inner = &inner_cache.comps;
    let inner_idx = &inner_cache.index;
    let mut best: Option<TemplateResult> = None;

    // Invertible gates (XOR, ADD): hash lookup.
    for &g_out in &ALL_GATES {
        if !gate_invertible(g_out) {
            continue;
        }
        // Case A: G_out(atom, inner_comp)
        for ai in pool {
            let res = target.residual(&ai.vals, g_out, mask);
            let Some(slot) = inner_idx.find(&res) else {
                continue;
            };
            let inner_e = make_inner(pool, &inner[slot]);
            let e = gate_expr(g_out, ai.expr.clone_tree(), inner_e);
            try_update(&mut best, e, eval, nv, bw, baseline);
        }
        if best.is_some() {
            return best;
        }
    }
    for &g_out in &ALL_GATES {
        if !gate_invertible(g_out) {
            continue;
        }
        // Case B: G_out(inner_comp, inner_comp)
        for ii in 0..inner.len() {
            let res = target.residual(&inner[ii].vals, g_out, mask);
            let Some(slot) = inner_idx.find(&res) else {
                continue;
            };
            let lhs = make_inner(pool, &inner[ii]);
            let rhs = make_inner(pool, &inner[slot]);
            let e = gate_expr(g_out, lhs, rhs);
            try_update(&mut best, e, eval, nv, bw, baseline);
        }
        if best.is_some() {
            return best;
        }
    }

    // AND/OR: pre-filtered compatible scan.
    let compat_pool_and = collect_compatible_atoms(pool, target, Gate::And);
    let compat_pool_or = collect_compatible_atoms(pool, target, Gate::Or);
    let compat_inner_and = collect_compatible_inner(inner, target, Gate::And);
    let compat_inner_or = collect_compatible_inner(inner, target, Gate::Or);

    for &g_out in &[Gate::And, Gate::Or] {
        let pool_compat = if matches!(g_out, Gate::And) {
            &compat_pool_and
        } else {
            &compat_pool_or
        };
        let inner_compat = if matches!(g_out, Gate::And) {
            &compat_inner_and
        } else {
            &compat_inner_or
        };
        for &ai_idx in pool_compat {
            let ai = &pool[ai_idx];
            for &ii_idx in inner_compat {
                let ii = &inner[ii_idx];
                if !probe0_matches(ai.vals.0[0], ii.vals.0[0], target.0[0], g_out, mask) {
                    continue;
                }
                let matches_target = match g_out {
                    Gate::And => and_matches(&ai.vals, &ii.vals, target),
                    Gate::Or => or_matches(&ai.vals, &ii.vals, target),
                    _ => unreachable!(),
                };
                if !matches_target {
                    continue;
                }
                let e = gate_expr(g_out, ai.expr.clone_tree(), make_inner(pool, ii));
                if try_update(&mut best, e, eval, nv, bw, baseline) {
                    return best;
                }
            }
        }
        if best.is_some() {
            return best;
        }
    }

    // MUL: probe-0 bucketed scan, fallback to full scan.
    let mut mul_candidates: Vec<usize> = Vec::new();
    for ai in pool {
        let used_filter = collect_mul_probe0_candidates(
            &inner_cache.mul_probe0_buckets,
            ai.vals.0[0],
            target.0[0],
            bw,
            &mut mul_candidates,
        );
        if used_filter {
            for &ii_idx in &mul_candidates {
                let ii = &inner[ii_idx];
                if !mul_matches(&ai.vals, &ii.vals, target, mask, 1) {
                    continue;
                }
                let e = gate_expr(Gate::Mul, ai.expr.clone_tree(), make_inner(pool, ii));
                if try_update(&mut best, e, eval, nv, bw, baseline) {
                    return best;
                }
            }
            continue;
        }
        for ii in inner {
            if !mul_matches(&ai.vals, &ii.vals, target, mask, 0) {
                continue;
            }
            let e = gate_expr(Gate::Mul, ai.expr.clone_tree(), make_inner(pool, ii));
            if try_update(&mut best, e, eval, nv, bw, baseline) {
                return best;
            }
        }
    }

    best
}

// ---------------------------------------------------------------
// Layer 3: target = G1(A, G2(B, R))   G1, G2 invertible
// ---------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn layer3(
    target: &ProbeVals,
    pool: &[Atom],
    vmap: &ValMap,
    inner_cache: &InnerCompositions,
    mask: u64,
    eval: &Evaluator,
    nv: u32,
    bw: u32,
    baseline: Option<&ExprCost>,
) -> Option<TemplateResult> {
    let inner = &inner_cache.comps;
    let inner_idx = &inner_cache.index;
    let pn = pool.len();
    for &g1 in &ALL_GATES {
        if !gate_invertible(g1) {
            continue;
        }
        for ai in 0..pn {
            let r1 = target.residual(&pool[ai].vals, g1, mask);
            if vmap.contains(&r1) {
                continue;
            }
            for &g2 in &ALL_GATES {
                if !gate_invertible(g2) {
                    continue;
                }
                for bi in 0..pn {
                    let r2 = r1.residual(&pool[bi].vals, g2, mask);
                    let r2_expr: Option<Box<Expr>> = vmap
                        .find(&r2)
                        .map(|p| pool[p].expr.clone_tree())
                        .or_else(|| inner_idx.find(&r2).map(|p| make_inner(pool, &inner[p])));
                    let Some(r2_e) = r2_expr else {
                        continue;
                    };
                    let mid = gate_expr(g2, pool[bi].expr.clone_tree(), r2_e);
                    let candidate = gate_expr(g1, pool[ai].expr.clone_tree(), mid);
                    let chk = full_width_check_eval(eval, nv, &candidate, bw, DEFAULT_NUM_SAMPLES);
                    if !chk.passed {
                        continue;
                    }
                    let info = compute_cost(&candidate);
                    if let Some(b) = baseline {
                        if !is_better(&info.cost, b) {
                            continue;
                        }
                    }
                    return Some(TemplateResult {
                        expr: candidate,
                        cost: info.cost,
                        verification: VerificationState::Verified,
                    });
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------
// Layer 4: target = G1(A, Unary(G2(B, inner_C)))
//          G1 invertible; Unary ∈ {Neg, Not}; G2 ∈ {And, Or, Mul}
// ---------------------------------------------------------------

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn layer4(
    target: &ProbeVals,
    pool: &[Atom],
    vmap: &ValMap,
    inner_cache: &InnerCompositions,
    mask: u64,
    eval: &Evaluator,
    nv: u32,
    bw: u32,
    baseline: Option<&ExprCost>,
) -> Option<TemplateResult> {
    let inner = &inner_cache.comps;
    let inner_idx = &inner_cache.index;
    let mut best: Option<TemplateResult> = None;
    let pn = pool.len();
    let inn = inner.len();

    let mut mul_candidates: Vec<usize> = Vec::new();
    for &g1 in &ALL_GATES {
        if !gate_invertible(g1) {
            continue;
        }
        for ai in 0..pn {
            let r1 = target.residual(&pool[ai].vals, g1, mask);
            if vmap.contains(&r1) {
                continue;
            }

            for wrap in 0..2 {
                let mut lifted = ProbeVals::default();
                for i in 0..N_PROBES {
                    lifted.0[i] = if wrap == 0 {
                        r1.0[i].wrapping_neg() & mask
                    } else {
                        (!r1.0[i]) & mask
                    };
                }

                if let Some(p) = inner_idx.find(&lifted) {
                    let inner_e = make_inner(pool, &inner[p]);
                    let wrapped = if wrap == 0 {
                        Expr::neg(inner_e)
                    } else {
                        Expr::not(inner_e)
                    };
                    let e = gate_expr(g1, pool[ai].expr.clone_tree(), wrapped);
                    if try_update(&mut best, e, eval, nv, bw, baseline) {
                        return best;
                    }
                }

                for &g2 in &[Gate::And, Gate::Or] {
                    for bi in 0..pn {
                        if !compatible(&pool[bi].vals, &lifted, g2) {
                            continue;
                        }
                        let b0 = pool[bi].vals.0[0];
                        let t0 = lifted.0[0];
                        for (&key, bucket) in &inner_cache.mul_probe0_buckets {
                            if !probe0_matches(b0, key, t0, g2, mask) {
                                continue;
                            }
                            for &ii in bucket {
                                let matches_lifted = match g2 {
                                    Gate::And => {
                                        and_matches(&pool[bi].vals, &inner[ii].vals, &lifted)
                                    }
                                    Gate::Or => {
                                        or_matches(&pool[bi].vals, &inner[ii].vals, &lifted)
                                    }
                                    _ => unreachable!(),
                                };
                                if !matches_lifted {
                                    continue;
                                }
                                let g2_e = gate_expr(
                                    g2,
                                    pool[bi].expr.clone_tree(),
                                    make_inner(pool, &inner[ii]),
                                );
                                let wrapped = if wrap == 0 {
                                    Expr::neg(g2_e)
                                } else {
                                    Expr::not(g2_e)
                                };
                                let e = gate_expr(g1, pool[ai].expr.clone_tree(), wrapped);
                                if try_update(&mut best, e, eval, nv, bw, baseline) {
                                    return best;
                                }
                            }
                        }
                    }
                }

                for bi in 0..pn {
                    let filtered = collect_mul_probe0_candidates(
                        &inner_cache.mul_probe0_buckets,
                        pool[bi].vals.0[0],
                        lifted.0[0],
                        bw,
                        &mut mul_candidates,
                    );
                    if filtered {
                        for &ii_idx in &mul_candidates {
                            if !mul_matches(&pool[bi].vals, &inner[ii_idx].vals, &lifted, mask, 1) {
                                continue;
                            }
                            let g2_e = gate_expr(
                                Gate::Mul,
                                pool[bi].expr.clone_tree(),
                                make_inner(pool, &inner[ii_idx]),
                            );
                            let wrapped = if wrap == 0 {
                                Expr::neg(g2_e)
                            } else {
                                Expr::not(g2_e)
                            };
                            let e = gate_expr(g1, pool[ai].expr.clone_tree(), wrapped);
                            if try_update(&mut best, e, eval, nv, bw, baseline) {
                                return best;
                            }
                        }
                        continue;
                    }
                    for ii in 0..inn {
                        if !mul_matches(&pool[bi].vals, &inner[ii].vals, &lifted, mask, 0) {
                            continue;
                        }
                        let g2_e = gate_expr(
                            Gate::Mul,
                            pool[bi].expr.clone_tree(),
                            make_inner(pool, &inner[ii]),
                        );
                        let wrapped = if wrap == 0 {
                            Expr::neg(g2_e)
                        } else {
                            Expr::not(g2_e)
                        };
                        let e = gate_expr(g1, pool[ai].expr.clone_tree(), wrapped);
                        if try_update(&mut best, e, eval, nv, bw, baseline) {
                            return best;
                        }
                    }
                }
            }
        }
    }
    best
}

// ---------------------------------------------------------------
// Probe-point generation (deterministic SplitMix64).
// ---------------------------------------------------------------

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn make_probe_points(num_vars: u32, bw: u32) -> Vec<Vec<u64>> {
    let mask = bitmask(bw);
    let mut state: u64 = 0x000C_0B4A;
    let mut pts = Vec::with_capacity(N_PROBES);
    for _ in 0..N_PROBES {
        let mut row = vec![0u64; num_vars as usize];
        for slot in &mut row {
            *slot = splitmix64(&mut state) & mask;
        }
        pts.push(row);
    }
    pts
}

// ---------------------------------------------------------------
// Public entry point.
// ---------------------------------------------------------------

fn guard(msg: &'static str, sub: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category: ReasonCategory::GuardFailed,
                domain: ReasonDomain::TemplateDecomposer,
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
                domain: ReasonDomain::TemplateDecomposer,
                subcode: sub,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

#[allow(clippy::too_many_lines)]
pub fn try_template_decomposition(
    eval: Option<&Evaluator>,
    num_vars: u32,
    bitwidth: u32,
    baseline_cost: Option<&ExprCost>,
) -> SolverResult<TemplateResult> {
    let Some(eval) = eval else {
        return SolverResult::Inapplicable(guard("no evaluator available", subcode::NO_EVALUATOR));
    };
    if num_vars > MAX_VARS {
        return SolverResult::Inapplicable(guard("too many variables", subcode::TOO_MANY_VARS));
    }

    if num_vars == 0 {
        let val = eval.eval(&[]);
        let e = Expr::constant(val);
        let info = compute_cost(&e);
        if let Some(b) = baseline_cost {
            if !is_better(&info.cost, b) {
                return SolverResult::Blocked(guard(
                    "constant result not cheaper than baseline",
                    subcode::COST_REJECTED,
                ));
            }
        }
        return SolverResult::Success(TemplateResult {
            expr: e,
            cost: info.cost,
            verification: VerificationState::Verified,
        });
    }

    let mask = bitmask(bitwidth);
    let pts = make_probe_points(num_vars, bitwidth);

    let mut target = ProbeVals::default();
    for i in 0..N_PROBES {
        target.0[i] = eval.eval(&pts[i]) & mask;
    }

    let mut pool: Vec<Atom> = Vec::new();
    let mut vmap = ValMap::default();
    populate(&mut pool, &mut vmap, num_vars, &pts, bitwidth);

    // Direct atom hit on `target`.
    if let Some(slot) = vmap.find(&target) {
        let e = pool[slot].expr.clone_tree();
        let chk = full_width_check_eval(eval, num_vars, &e, bitwidth, DEFAULT_NUM_SAMPLES);
        if chk.passed {
            let info = compute_cost(&e);
            if baseline_cost.is_none_or(|b| is_better(&info.cost, b)) {
                return SolverResult::Success(TemplateResult {
                    expr: e,
                    cost: info.cost,
                    verification: VerificationState::Verified,
                });
            }
        }
    }

    if let Some(r) = layer1(
        &target,
        &pool,
        &vmap,
        mask,
        eval,
        num_vars,
        bitwidth,
        baseline_cost,
    ) {
        return SolverResult::Success(r);
    }

    let inner_cache = build_inner_compositions(&pool, &vmap, mask);
    if let Some(r) = layer2(
        &target,
        &pool,
        &inner_cache,
        mask,
        eval,
        num_vars,
        bitwidth,
        baseline_cost,
    ) {
        return SolverResult::Success(r);
    }

    // Unary wrap on target.
    for wrap in 0..2 {
        let lifted = if wrap == 0 {
            target.neg(mask)
        } else {
            target.not_op(mask)
        };
        let check_wrap = |inner_e: Box<Expr>| -> Option<TemplateResult> {
            let wrapped = if wrap == 0 {
                Expr::neg(inner_e)
            } else {
                Expr::not(inner_e)
            };
            let chk =
                full_width_check_eval(eval, num_vars, &wrapped, bitwidth, DEFAULT_NUM_SAMPLES);
            if !chk.passed {
                return None;
            }
            let info = compute_cost(&wrapped);
            if let Some(b) = baseline_cost {
                if !is_better(&info.cost, b) {
                    return None;
                }
            }
            Some(TemplateResult {
                expr: wrapped,
                cost: info.cost,
                verification: VerificationState::Verified,
            })
        };

        if let Some(slot) = vmap.find(&lifted) {
            if let Some(r) = check_wrap(pool[slot].expr.clone_tree()) {
                return SolverResult::Success(r);
            }
        }
        if let Some(w1) = layer1(&lifted, &pool, &vmap, mask, eval, num_vars, bitwidth, None) {
            if let Some(r) = check_wrap(w1.expr) {
                return SolverResult::Success(r);
            }
        }
    }

    if let Some(r) = layer3(
        &target,
        &pool,
        &vmap,
        &inner_cache,
        mask,
        eval,
        num_vars,
        bitwidth,
        baseline_cost,
    ) {
        return SolverResult::Success(r);
    }

    if let Some(r) = layer4(
        &target,
        &pool,
        &vmap,
        &inner_cache,
        mask,
        eval,
        num_vars,
        bitwidth,
        baseline_cost,
    ) {
        return SolverResult::Success(r);
    }

    SolverResult::Blocked(search_exhausted(
        "no template match found",
        subcode::NO_MATCH,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_evaluator_is_inapplicable() {
        let r = try_template_decomposition(None, 1, 64, None);
        assert!(matches!(r, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn too_many_vars_is_inapplicable() {
        let f = Expr::variable(0);
        let eval = Evaluator::from_expr(&f, 64);
        let r = try_template_decomposition(Some(&eval), 7, 64, None);
        assert!(matches!(r, SolverResult::Inapplicable(_)));
    }

    #[test]
    fn zero_vars_returns_constant() {
        let eval = Evaluator::from_closure(|_: &[u64]| 42u64);
        let SolverResult::Success(r) = try_template_decomposition(Some(&eval), 0, 64, None) else {
            panic!("expected success");
        };
        assert!(matches!(r.expr.kind, cobra_core::expr::Kind::Constant(_)));
    }

    #[test]
    fn layer1_recovers_xor() {
        // f = x ^ y — Layer 1 invertible-gate hash hit.
        let f = Expr::xor(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&f, 64);
        let SolverResult::Success(r) = try_template_decomposition(Some(&eval), 2, 64, None) else {
            panic!("expected success");
        };
        let chk = full_width_check_eval(&eval, 2, &r.expr, 64, DEFAULT_NUM_SAMPLES);
        assert!(chk.passed);
    }

    #[test]
    fn layer1_recovers_and() {
        // f = x & y — Layer 1 non-invertible scan with probe-0 reject.
        let f = Expr::and(Expr::variable(0), Expr::variable(1));
        let eval = Evaluator::from_expr(&f, 64);
        let SolverResult::Success(r) = try_template_decomposition(Some(&eval), 2, 64, None) else {
            panic!("expected success");
        };
        let chk = full_width_check_eval(&eval, 2, &r.expr, 64, DEFAULT_NUM_SAMPLES);
        assert!(chk.passed);
    }

    #[test]
    fn layer2_recovers_xor_of_and_or() {
        // f = (x & y) ^ (x | z) — needs Layer 2 (two-deep gate composition).
        let f = Expr::xor(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(2)),
        );
        let eval = Evaluator::from_expr(&f, 64);
        let r = try_template_decomposition(Some(&eval), 3, 64, None);
        let SolverResult::Success(t) = r else {
            panic!("expected success");
        };
        let chk = full_width_check_eval(&eval, 3, &t.expr, 64, DEFAULT_NUM_SAMPLES);
        assert!(chk.passed);
    }
}
