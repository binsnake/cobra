//! Multi-round XOR-lowering for mixed-product / bitwise-over-arith
//! sites. Walks the expression tree top-down, tracking whether each
//! sub-expression sits inside a mixed-product (`Mul(.., bitwise..)`)
//! or bitwise-over-arith context, and rewrites
//!     `x ^ y  →  x + y - 2 * (x & y)`
//! at every `Xor` site within such a context.
//!
//! Each round re-classifies the result and keeps it only when:
//!   - node count stays under `max_node_growth × initial`,
//!   - no new unsupported flag appeared, and
//!   - either the unsupported-flag set shrank (coarse progress) or
//!     the rewriteable-site count went down (fine progress).

use cobra_core::classification::{needs_structural_recovery, StructuralFlag};
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_rewrite::has_nonleaf_bitwise;
use cobra_core::expr_utils::has_var_dep;

use crate::classifier::classify_structural;

#[derive(Copy, Clone, Default)]
struct RewriteContext {
    in_mixed_product: bool,
    in_bitwise_over_arith: bool,
}

impl RewriteContext {
    fn unsupported(self) -> bool {
        self.in_mixed_product || self.in_bitwise_over_arith
    }
}

#[derive(Clone, Copy)]
pub struct RewriteOptions {
    pub max_rounds: u32,
    pub max_node_growth: u32,
    pub bitwidth: u32,
}

#[derive(Clone)]
pub struct RewriteResult {
    pub expr: Box<Expr>,
    pub rounds_applied: u32,
    pub structure_changed: bool,
}

fn has_arith_var(expr: &Expr) -> bool {
    if matches!(expr.kind, Kind::Add | Kind::Mul | Kind::Neg) && has_var_dep(expr) {
        return true;
    }
    expr.children.iter().any(|c| has_arith_var(c))
}

fn child_context(expr: &Expr, parent: RewriteContext) -> RewriteContext {
    let mut ctx = parent;
    if matches!(expr.kind, Kind::Mul) && expr.children.len() == 2 {
        let lhs_bw = has_nonleaf_bitwise(&expr.children[0]);
        let rhs_bw = has_nonleaf_bitwise(&expr.children[1]);
        let lhs_vd = has_var_dep(&expr.children[0]);
        let rhs_vd = has_var_dep(&expr.children[1]);
        if (lhs_bw || rhs_bw) && lhs_vd && rhs_vd {
            ctx.in_mixed_product = true;
        }
    }
    if matches!(expr.kind, Kind::And | Kind::Or | Kind::Xor)
        && expr.children.len() == 2
        && (has_arith_var(&expr.children[0]) || has_arith_var(&expr.children[1]))
    {
        ctx.in_bitwise_over_arith = true;
    }
    if matches!(expr.kind, Kind::Not)
        && !expr.children.is_empty()
        && has_arith_var(&expr.children[0])
    {
        ctx.in_bitwise_over_arith = true;
    }
    ctx
}

fn count_sites_impl(expr: &Expr, ctx: RewriteContext) -> u32 {
    let mut count = 0u32;
    let child_ctx = child_context(expr, ctx);
    if matches!(expr.kind, Kind::Xor) && expr.children.len() == 2 && child_ctx.unsupported() {
        count += 1;
    }
    for c in &expr.children {
        count += count_sites_impl(c, child_ctx);
    }
    count
}

#[must_use]
pub fn count_rewriteable_sites(expr: &Expr) -> u32 {
    count_sites_impl(expr, RewriteContext::default())
}

#[must_use]
pub fn node_count(expr: &Expr) -> u32 {
    let mut n = 1u32;
    for c in &expr.children {
        n += node_count(c);
    }
    n
}

/// Single-pass fusion of `count_rewriteable_sites` + `node_count`.
/// Returns `(sites, nodes)` in one traversal, saving a walk per rewrite round.
fn count_sites_and_nodes_impl(expr: &Expr, ctx: RewriteContext) -> (u32, u32) {
    let child_ctx = child_context(expr, ctx);
    let mut sites = 0u32;
    let mut nodes = 1u32;
    if matches!(expr.kind, Kind::Xor) && expr.children.len() == 2 && child_ctx.unsupported() {
        sites += 1;
    }
    for c in &expr.children {
        let (cs, cn) = count_sites_and_nodes_impl(c, child_ctx);
        sites += cs;
        nodes += cn;
    }
    (sites, nodes)
}

fn count_sites_and_nodes(expr: &Expr) -> (u32, u32) {
    count_sites_and_nodes_impl(expr, RewriteContext::default())
}

#[allow(clippy::boxed_local)]
fn apply_xor_lowering(expr: Box<Expr>, ctx: RewriteContext) -> Box<Expr> {
    let mut e = *expr;
    let child_ctx = child_context(&e, ctx);
    for i in 0..e.children.len() {
        let child = std::mem::replace(&mut e.children[i], Expr::constant(0));
        e.children[i] = apply_xor_lowering(child, child_ctx);
    }
    if matches!(e.kind, Kind::Xor) && child_ctx.unsupported() && e.children.len() == 2 {
        let lhs = e.children[0].clone_tree();
        let rhs = e.children[1].clone_tree();
        let lhs2 = e.children[0].clone_tree();
        let rhs2 = e.children[1].clone_tree();
        let sum = Expr::add(lhs, rhs);
        let and_term = Expr::and(lhs2, rhs2);
        let two_and = Expr::mul(Expr::constant(2), and_term);
        let neg_two_and = Expr::neg(two_and);
        return Expr::add(sum, neg_two_and);
    }
    Box::new(e)
}

#[must_use]
pub fn rewrite_mixed_products(expr: Box<Expr>, opts: &RewriteOptions) -> RewriteResult {
    let cls = classify_structural(&expr);
    let unsupported_mask =
        StructuralFlag::HAS_MIXED_PRODUCT | StructuralFlag::HAS_BITWISE_OVER_ARITH;
    let _ = needs_structural_recovery;
    if cls.flags.contains(StructuralFlag::HAS_UNKNOWN_SHAPE)
        || (cls.flags & unsupported_mask).bits() == 0
        || count_rewriteable_sites(&expr) == 0
    {
        return RewriteResult {
            expr,
            rounds_applied: 0,
            structure_changed: false,
        };
    }

    let (initial_sites, initial_count) = count_sites_and_nodes(&expr);
    let mut old_flags = cls.flags & unsupported_flag_mask();
    let mut old_sites = initial_sites;

    let mut result = RewriteResult {
        expr,
        rounds_applied: 0,
        structure_changed: false,
    };

    for round in 1..=opts.max_rounds {
        let new_expr = apply_xor_lowering(result.expr.clone_tree(), RewriteContext::default());
        let (new_sites, new_count) = count_sites_and_nodes(&new_expr);
        if new_count > initial_count.saturating_mul(opts.max_node_growth) {
            break;
        }
        let new_cls = classify_structural(&new_expr);
        let new_flags = new_cls.flags & unsupported_flag_mask();

        if (new_flags & !old_flags).bits() != 0 {
            break;
        }
        let coarse_progress = new_flags != old_flags && (new_flags & old_flags) == new_flags;
        let fine_progress = new_sites < old_sites;
        if !coarse_progress && !fine_progress {
            break;
        }

        result.expr = new_expr;
        old_flags = new_flags;
        old_sites = new_sites;
        result.structure_changed = true;
        result.rounds_applied = round;
        if new_sites == 0 {
            break;
        }
    }
    result
}

fn unsupported_flag_mask() -> StructuralFlag {
    StructuralFlag::HAS_MIXED_PRODUCT
        | StructuralFlag::HAS_BITWISE_OVER_ARITH
        | StructuralFlag::HAS_UNKNOWN_SHAPE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn count_zero_for_pure_arithmetic() {
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        assert_eq!(count_rewriteable_sites(&e), 0);
    }

    #[test]
    fn lowers_xor_inside_mul_with_bitwise_lhs() {
        // (x ^ y) * z — Xor sits inside a mixed-product context.
        let e = Expr::mul(
            Expr::xor(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        assert!(count_rewriteable_sites(&e) >= 1);
        let opts = RewriteOptions {
            max_rounds: 2,
            max_node_growth: 5,
            bitwidth: 64,
        };
        let r = rewrite_mixed_products(e, &opts);
        assert!(r.structure_changed);
        // Top-level becomes Mul(Add(...), variable(2)) — the Add reflects
        // the substitution x ^ y → x + y - 2*(x&y).
        assert!(matches!(r.expr.kind, Kind::Mul));
    }

    #[test]
    fn pure_xor_with_no_mixed_context_is_left_alone() {
        let e = Expr::xor(Expr::variable(0), Expr::variable(1));
        let opts = RewriteOptions {
            max_rounds: 2,
            max_node_growth: 5,
            bitwidth: 64,
        };
        let r = rewrite_mixed_products(e, &opts);
        assert!(!r.structure_changed);
    }
}
