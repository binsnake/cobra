//! `AtomIdentityRewrite` — rewrites bitwise identities that hold over
//! arbitrary integer atoms (not just boolean-valued subterms). The
//! matcher walks the AST bottom-up, pattern-matches a small closed set
//! of identity LHS templates, and verifies the RHS candidate with a
//! 256-sample full-width spot check before accepting.
//!
//! Recognised identities (all hold at full width for arbitrary A, B, X):
//!
//! | LHS                             | RHS      |
//! |---------------------------------|----------|
//! | `(A \| B) - (A & B)`            | `A ^ B`  |
//! | `(~A \| B) - ~A`                | `A & B`  |
//! | `(~A \| X) + A + 1`             | `A & X`  |
//! | `A - B - 2*(A \| ~B) - 2`       | `A ^ B`  |
//!
//! These shapes show up in the Syntia benchmark suite where the
//! signature-based pattern matcher can't recover them — their boolean
//! signature is a simple function but the full-width arithmetic form
//! isn't equal to the boolean candidate. Verified structurally and
//! gated by `is_better(candidate_cost, baseline_cost)` so the rewrite
//! is strictly cheaper than the matched subtree.

use cobra_core::arith::bitmask;
use cobra_core::expr::{Expr, Kind};
use cobra_core::expr_cost::{compute_cost, is_better};
use cobra_core::pass_contract::ReasonDetail;
use cobra_core::result::Result;
use cobra_core::spot_check::full_width_check_eval;

use cobra_orchestrator::{
    expr_identity_hash, replace_by_hash, AstPayload, ItemDisposition, OrchestratorContext,
    PassDecision, PassResult, Provenance, StateData, WorkItem,
};

use crate::classifier::classify_structural;

// ---------- entry point ----------

#[must_use]
pub fn applicable(item: &WorkItem, _ctx: &OrchestratorContext) -> bool {
    matches!(item.payload, StateData::FoldedAst(_))
}

/// Bottom-up sweep: apply the atom-identity rewrites at seed time,
/// before classification. Lets Linear-classified inputs (e.g. the
/// syntia XOR-identity cases) benefit — the in-pipeline pass only
/// runs on exploration-candidate items. Returns a rewritten tree;
/// callers detect changes by comparing against the input.
#[must_use]
pub fn apply_atom_identities(mut expr: Box<Expr>, bitwidth: u32) -> Box<Expr> {
    let children: Vec<Box<Expr>> = expr.children.drain(..).collect();
    for child in children {
        expr.children.push(apply_atom_identities(child, bitwidth));
    }
    let candidates = try_match_all(&expr, bitwidth);
    if candidates.is_empty() {
        return expr;
    }
    let baseline = compute_cost(&expr).cost;
    let eval = cobra_core::evaluator::Evaluator::from_expr(&expr, bitwidth);
    let num_vars = eval.input_arity();
    for candidate in candidates {
        if !is_better(&compute_cost(&candidate).cost, &baseline) {
            continue;
        }
        if !full_width_check_eval(&eval, num_vars, &candidate, bitwidth, 256).passed {
            continue;
        }
        // Re-run bottom-up on the new tree — the rewrite may have
        // exposed another identity.
        return apply_atom_identities(candidate, bitwidth);
    }
    expr
}

#[allow(clippy::unnecessary_wraps)]
pub fn run_atom_identity_rewrite(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    let StateData::FoldedAst(ast) = &item.payload else {
        return Ok(PassResult {
            decision: PassDecision::NotApplicable,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let Some(site) = find_first_rewrite_site(&ast.expr, ctx.bitwidth) else {
        return Ok(PassResult {
            decision: PassDecision::NoProgress,
            disposition: ItemDisposition::RetainCurrent,
            next: Vec::new(),
            reason: ReasonDetail::default(),
        });
    };

    let rewritten = rewrite_at_site(ast, item, site);
    Ok(PassResult {
        decision: PassDecision::Advance,
        disposition: ItemDisposition::ConsumeCurrent,
        next: vec![rewritten],
        reason: ReasonDetail::default(),
    })
}

struct RewriteSite {
    /// Hash of the node whose subtree is replaced.
    target_hash: u64,
    candidate: Box<Expr>,
}

// Bottom-up walk: find the deepest node whose subtree matches one of
// our identities. Returns `Some(site)` on the first hit. Each candidate
// must beat baseline cost AND pass a 256-sample spot-check against the
// matched subtree's evaluator.
fn find_first_rewrite_site(root: &Expr, bitwidth: u32) -> Option<RewriteSite> {
    for child in &root.children {
        if let Some(s) = find_first_rewrite_site(child, bitwidth) {
            return Some(s);
        }
    }
    let candidates = try_match_all(root, bitwidth);
    if candidates.is_empty() {
        return None;
    }
    let baseline = compute_cost(root).cost;
    let eval = cobra_core::evaluator::Evaluator::from_expr(root, bitwidth);
    let num_vars = eval.input_arity();
    for candidate in candidates {
        if !is_better(&compute_cost(&candidate).cost, &baseline) {
            continue;
        }
        if !full_width_check_eval(&eval, num_vars, &candidate, bitwidth, 256).passed {
            continue;
        }
        return Some(RewriteSite {
            target_hash: expr_identity_hash(root),
            candidate,
        });
    }
    None
}

fn rewrite_at_site(ast: &AstPayload, item: &WorkItem, site: RewriteSite) -> WorkItem {
    let mut repl = Some(site.candidate);
    let (rebuilt, _) = replace_by_hash(ast.expr.clone_tree(), site.target_hash, &mut repl);
    let new_cls = classify_structural(&rebuilt);
    let solve_ctx = ast.solve_ctx.clone();
    let mut rewritten = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rebuilt,
        classification: Some(new_cls),
        provenance: Provenance::Rewritten,
        solve_ctx,
    })));
    rewritten.features = item.features.clone();
    rewritten.features.classification = Some(new_cls);
    rewritten.features.provenance = Provenance::Rewritten;
    rewritten.metadata = item.metadata.clone();
    rewritten.depth = item.depth;
    rewritten.rewrite_gen = item.rewrite_gen + 1;
    rewritten.attempted_mask = 0;
    rewritten.group_id = item.group_id;
    rewritten.history.clone_from(&item.history);
    rewritten.history.push(cobra_orchestrator::PassId::AtomIdentityRewrite);
    rewritten
}

// ---------- identity matchers ----------

/// Collect all plausible candidate rewrites for `node`. The caller
/// verifies each with a full-width spot check. Permissive matchers
/// (suffix `_lax`) rely on that check to reject unmatched shapes —
/// they emit candidates for any Or/And/Not pattern that *could* be
/// the LHS of one of our identities, regardless of the surrounding
/// addends. The spot check has false-positive rate ≈ 2^-256 × 256 ≈
/// 2^-248 per try, so it's safe to be loose here.
fn try_match_all(node: &Expr, bitwidth: u32) -> Vec<Box<Expr>> {
    let mut out = Vec::new();
    if let Some(c) = match_xor_via_or_minus_and(node) {
        out.push(c);
    }
    if let Some(c) = match_and_via_not_or_minus_not(node) {
        out.push(c);
    }
    if let Some(c) = match_and_via_not_or_plus_a_plus_one(node, bitwidth) {
        out.push(c);
    }
    if let Some(c) = match_xor_via_ornot_flat(node, bitwidth) {
        out.push(c);
    }
    // Relaxed matchers — try every Or-with-Not site in the addend list
    // and emit candidate `A & Y` / `A ^ Y` shapes. Catches cases where
    // constant folding or seed-time pattern simplification has rewritten
    // the strict 3/4-term forms.
    match_and_via_ornot_lax(node, &mut out);
    match_xor_via_ornot_lax(node, &mut out);
    out
}

/// `(A | B) - (A & B)  →  A ^ B`
fn match_xor_via_or_minus_and(node: &Expr) -> Option<Box<Expr>> {
    let (lhs, rhs_neg) = match_binary_add_with_neg(node)?;
    // One side is an Or, the other (after peeling Neg) is an And with
    // the same two operands (either order).
    let (or_side, and_side) = pick_or_and(lhs, rhs_neg)?;
    let (a, b) = (&or_side.children[0], &or_side.children[1]);
    let (x, y) = (&and_side.children[0], &and_side.children[1]);
    if !exprs_equal_as_unordered_pair(a, b, x, y) {
        return None;
    }
    Some(Expr::xor(a.clone_tree(), b.clone_tree()))
}

/// `(~A | B) - ~A  →  A & B`
fn match_and_via_not_or_minus_not(node: &Expr) -> Option<Box<Expr>> {
    let (lhs, rhs_neg) = match_binary_add_with_neg(node)?;
    // Identify the Or side and the Not side after peeling Neg.
    let or_side = pick_kind(lhs, rhs_neg, Kind::Or)?;
    let not_side = pick_other(lhs, rhs_neg, or_side)?;
    if !matches!(not_side.kind, Kind::Not) || not_side.children.len() != 1 {
        return None;
    }
    let a_inside_not = &not_side.children[0];
    // Or's children: one must be Not(A) where A ≡ a_inside_not. The
    // other is B.
    let (or_left, or_right) = (&or_side.children[0], &or_side.children[1]);
    let a_expr = a_inside_not.clone_tree();
    let b_expr = if is_not_of(or_left, a_inside_not) {
        or_right.clone_tree()
    } else if is_not_of(or_right, a_inside_not) {
        or_left.clone_tree()
    } else {
        return None;
    };
    Some(Expr::and(a_expr, b_expr))
}

/// `(~A | X) + A + 1  →  A & X`
fn match_and_via_not_or_plus_a_plus_one(node: &Expr, bitwidth: u32) -> Option<Box<Expr>> {
    let mask = bitmask(bitwidth);
    let addends = flatten_addends(node);
    // Three terms, all positive: one `Or(Not(A), X)`, one `A`, and one
    // `Constant(1)` (mod mask).
    if addends.len() != 3 {
        return None;
    }
    if addends.iter().any(|a| a.negated) {
        return None;
    }
    let one_idx = addends
        .iter()
        .position(|a| matches!(a.expr.kind, Kind::Constant(v) if (v & mask) == 1))?;
    let or_idx = addends
        .iter()
        .enumerate()
        .find(|(i, a)| *i != one_idx && matches!(a.expr.kind, Kind::Or))
        .map(|(i, _)| i)?;
    let a_idx = (0..3)
        .find(|i| *i != one_idx && *i != or_idx)
        .expect("3 - 2 = 1 remaining index");

    let or_expr = addends[or_idx].expr;
    if or_expr.children.len() != 2 {
        return None;
    }
    let a_expr = addends[a_idx].expr;
    // One Or child is Not(A); the other is X.
    let (or_left, or_right) = (&or_expr.children[0], &or_expr.children[1]);
    let x_expr = if is_not_of(or_left, a_expr) {
        or_right.clone_tree()
    } else if is_not_of(or_right, a_expr) {
        or_left.clone_tree()
    } else {
        return None;
    };
    Some(Expr::and(a_expr.clone_tree(), x_expr))
}

/// `A - B - 2*(A | ~B) - 2  →  A ^ B`
fn match_xor_via_ornot_flat(node: &Expr, bitwidth: u32) -> Option<Box<Expr>> {
    let mask = bitmask(bitwidth);
    let addends = flatten_addends(node);
    // Expect exactly 4 addends: +A, -B, -2*(A|~B), -2. Matchers below
    // are commutative across the addend list.
    if addends.len() != 4 {
        return None;
    }

    // Locate the `-2` constant term (negated with magnitude 2 mod mask).
    let neg_two_idx = addends.iter().position(|a| {
        a.negated && matches!(a.expr.kind, Kind::Constant(v) if (v & mask) == 2)
    })?;

    // Locate the `-2*(A|~B)` term: negated with shape `Mul(Const(2), Or)`
    // or `Mul(Or, Const(2))`.
    let two_or_idx = addends.iter().enumerate().find_map(|(i, a)| {
        if i == neg_two_idx || !a.negated {
            return None;
        }
        let Kind::Mul = a.expr.kind else {
            return None;
        };
        if a.expr.children.len() != 2 {
            return None;
        }
        let (ch0, ch1) = (&a.expr.children[0], &a.expr.children[1]);
        let or_node = if matches!(ch0.kind, Kind::Constant(v) if (v & mask) == 2)
            && matches!(ch1.kind, Kind::Or)
        {
            ch1.as_ref()
        } else if matches!(ch1.kind, Kind::Constant(v) if (v & mask) == 2)
            && matches!(ch0.kind, Kind::Or)
        {
            ch0.as_ref()
        } else {
            return None;
        };
        if or_node.children.len() != 2 {
            return None;
        }
        Some((i, or_node))
    })?;

    let (mul_idx, or_node) = two_or_idx;

    // Remaining two addends must be `+A` and `-B` (order-independent).
    let remaining: Vec<usize> = (0..4).filter(|i| *i != neg_two_idx && *i != mul_idx).collect();
    if remaining.len() != 2 {
        return None;
    }
    let (a_idx, b_idx_candidate) = {
        let (i, j) = (remaining[0], remaining[1]);
        match (addends[i].negated, addends[j].negated) {
            (false, true) => (i, j),
            (true, false) => (j, i),
            _ => return None,
        }
    };
    let a_expr = addends[a_idx].expr;
    let b_expr = addends[b_idx_candidate].expr;

    // Or's children must be {A, Not(B)} in some order.
    let (ol, or_r) = (&or_node.children[0], &or_node.children[1]);
    let ok = (expr_eq(ol, a_expr) && is_not_of(or_r, b_expr))
        || (expr_eq(or_r, a_expr) && is_not_of(ol, b_expr));
    if !ok {
        return None;
    }

    Some(Expr::xor(a_expr.clone_tree(), b_expr.clone_tree()))
}

/// Relaxed Identity 3 matcher: for any positive-signed `Or(Not(A), Y)`
/// or `Or(Y, Not(A))` addend, emit candidate `A & Y`. The full-width
/// check in the caller verifies whether the full identity holds; this
/// lets us catch shapes like `(~X|Y) + A + 2` where constant folding
/// has reshuffled the 3-term form.
fn match_and_via_ornot_lax(node: &Expr, out: &mut Vec<Box<Expr>>) {
    if !matches!(node.kind, Kind::Add) {
        return;
    }
    let addends = flatten_addends(node);
    let mut seen: std::collections::HashSet<u64> = std::collections::HashSet::new();
    for a in &addends {
        if a.negated {
            continue;
        }
        let Kind::Or = a.expr.kind else {
            continue;
        };
        if a.expr.children.len() != 2 {
            continue;
        }
        let (ol, or_r) = (&a.expr.children[0], &a.expr.children[1]);
        let try_emit = |inner: &Expr, other: &Expr, out: &mut Vec<Box<Expr>>| {
            let cand = Expr::and(inner.clone_tree(), other.clone_tree());
            let hash = expr_identity_hash(&cand);
            out.push(cand);
            hash
        };
        if matches!(ol.kind, Kind::Not) && ol.children.len() == 1 {
            let h = try_emit(&ol.children[0], or_r, out);
            seen.insert(h);
        }
        if matches!(or_r.kind, Kind::Not) && or_r.children.len() == 1 {
            let h = try_emit(&or_r.children[0], ol, out);
            let _ = seen.insert(h);
        }
    }
}

/// Relaxed Identity 4 matcher: for any `Or(A, Not(B))` or
/// `Or(Not(B), A)` subterm appearing as a top-level addend — either
/// directly, or inside a `Mul(const, Or)` — emit candidate `A ^ B`.
/// Catches the `A - B - 2*(A|~B) - 2 = A^B` shape across multiple
/// surface forms: before constant folding (doubled Or addends), after
/// folding (Mul(2, Or)), and whatever partial mixes the parser and
/// pattern simplifier leave behind. The full-width check in the caller
/// gates correctness.
fn match_xor_via_ornot_lax(node: &Expr, out: &mut Vec<Box<Expr>>) {
    if !matches!(node.kind, Kind::Add) {
        return;
    }
    let addends = flatten_addends(node);
    for a in &addends {
        let or_node: Option<&Expr> = match a.expr.kind {
            Kind::Or if a.expr.children.len() == 2 => Some(a.expr),
            Kind::Mul if a.expr.children.len() == 2 => {
                let (m0, m1) = (&a.expr.children[0], &a.expr.children[1]);
                if matches!(m0.kind, Kind::Constant(_))
                    && matches!(m1.kind, Kind::Or)
                    && m1.children.len() == 2
                {
                    Some(m1.as_ref())
                } else if matches!(m1.kind, Kind::Constant(_))
                    && matches!(m0.kind, Kind::Or)
                    && m0.children.len() == 2
                {
                    Some(m0.as_ref())
                } else {
                    None
                }
            }
            _ => None,
        };
        let Some(or_node) = or_node else {
            continue;
        };
        let (ol, or_r) = (&or_node.children[0], &or_node.children[1]);
        if matches!(or_r.kind, Kind::Not) && or_r.children.len() == 1 {
            out.push(Expr::xor(
                ol.clone_tree(),
                or_r.children[0].clone_tree(),
            ));
        }
        if matches!(ol.kind, Kind::Not) && ol.children.len() == 1 {
            out.push(Expr::xor(
                or_r.clone_tree(),
                ol.children[0].clone_tree(),
            ));
        }
    }
}

// ---------- helpers ----------

struct Addend<'a> {
    expr: &'a Expr,
    negated: bool,
}

/// Flatten `Add(Add(...), x)` chains into a flat list of (sign, expr)
/// addends. `Neg(x)` is recorded as a negated entry; constant folding
/// isn't attempted here — callers must accept both `+Neg(2)` and
/// `-2`-as-constant shapes if they want them to be equivalent.
fn flatten_addends(node: &Expr) -> Vec<Addend<'_>> {
    let mut out = Vec::new();
    push_addend(node, false, &mut out);
    out
}

fn push_addend<'a>(node: &'a Expr, negated: bool, out: &mut Vec<Addend<'a>>) {
    match node.kind {
        Kind::Add if node.children.len() == 2 => {
            push_addend(&node.children[0], negated, out);
            push_addend(&node.children[1], negated, out);
        }
        Kind::Neg if node.children.len() == 1 => {
            push_addend(&node.children[0], !negated, out);
        }
        _ => out.push(Addend {
            expr: node,
            negated,
        }),
    }
}

/// Match `Add(X, Neg(Y))` or `Add(Neg(Y), X)` shapes. Returns
/// `(X_ref, Y_ref)` where Y has been peeled out of the `Neg`.
fn match_binary_add_with_neg(node: &Expr) -> Option<(&Expr, &Expr)> {
    if !matches!(node.kind, Kind::Add) || node.children.len() != 2 {
        return None;
    }
    let (l, r) = (&node.children[0], &node.children[1]);
    let is_neg = |e: &Expr| matches!(e.kind, Kind::Neg) && e.children.len() == 1;
    if is_neg(l) {
        Some((r, &l.children[0]))
    } else if is_neg(r) {
        Some((l, &r.children[0]))
    } else {
        None
    }
}

/// Given an Or node and a peeled `~`-side or And node, pair them up
/// based on kind — the Or must be the Or, the other must be an And
/// with exactly two children.
fn pick_or_and<'a>(lhs: &'a Expr, rhs: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    let is_or2 = |e: &Expr| matches!(e.kind, Kind::Or) && e.children.len() == 2;
    let is_and2 = |e: &Expr| matches!(e.kind, Kind::And) && e.children.len() == 2;
    if is_or2(lhs) && is_and2(rhs) {
        Some((lhs, rhs))
    } else if is_or2(rhs) && is_and2(lhs) {
        Some((rhs, lhs))
    } else {
        None
    }
}

fn pick_kind<'a>(lhs: &'a Expr, rhs: &'a Expr, kind: Kind) -> Option<&'a Expr> {
    let matches_kind = |e: &Expr| std::mem::discriminant(&e.kind) == std::mem::discriminant(&kind);
    if matches_kind(lhs) && lhs.children.len() == 2 {
        Some(lhs)
    } else if matches_kind(rhs) && rhs.children.len() == 2 {
        Some(rhs)
    } else {
        None
    }
}

fn pick_other<'a>(lhs: &'a Expr, rhs: &'a Expr, picked: &'a Expr) -> Option<&'a Expr> {
    if std::ptr::eq(lhs, picked) {
        Some(rhs)
    } else {
        Some(lhs)
    }
}

/// `true` if `n == Not(inner)` (one-child Not whose child is
/// structurally equal to `inner`).
fn is_not_of(n: &Expr, inner: &Expr) -> bool {
    matches!(n.kind, Kind::Not) && n.children.len() == 1 && expr_eq(&n.children[0], inner)
}

/// Structural equality of the unordered pair `{a, b}` against `{x, y}`.
fn exprs_equal_as_unordered_pair(a: &Expr, b: &Expr, x: &Expr, y: &Expr) -> bool {
    (expr_eq(a, x) && expr_eq(b, y)) || (expr_eq(a, y) && expr_eq(b, x))
}

#[inline]
fn expr_eq(lhs: &Expr, rhs: &Expr) -> bool {
    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xor_via_or_minus_and_two_vars() {
        // (x | y) - (x & y)  →  x ^ y
        let lhs = Expr::add(
            Expr::or(Expr::variable(0), Expr::variable(1)),
            Expr::neg(Expr::and(Expr::variable(0), Expr::variable(1))),
        );
        let cand = match_xor_via_or_minus_and(&lhs).expect("match");
        assert!(matches!(cand.kind, Kind::Xor));
    }

    #[test]
    fn and_via_not_or_minus_not_matches() {
        // (~a | b) - ~a  →  a & b
        let a = Expr::variable(0);
        let b = Expr::variable(1);
        let lhs = Expr::add(
            Expr::or(Expr::not(a.clone_tree()), b.clone_tree()),
            Expr::neg(Expr::not(a.clone_tree())),
        );
        let cand = match_and_via_not_or_minus_not(&lhs).expect("match");
        assert!(matches!(cand.kind, Kind::And));
    }

    #[test]
    fn and_via_not_or_plus_a_plus_one_matches() {
        // (~a | x) + a + 1  →  a & x
        let a = Expr::variable(0);
        let x = Expr::variable(1);
        let lhs = Expr::add(
            Expr::add(
                Expr::or(Expr::not(a.clone_tree()), x.clone_tree()),
                a.clone_tree(),
            ),
            Expr::constant(1),
        );
        let cand = match_and_via_not_or_plus_a_plus_one(&lhs, 64).expect("match");
        assert!(matches!(cand.kind, Kind::And));
    }

    #[test]
    fn xor_via_ornot_flat_matches() {
        // a - b - 2*(a | ~b) - 2  →  a ^ b
        let a = Expr::variable(0);
        let b = Expr::variable(1);
        let lhs = Expr::add(
            Expr::add(
                Expr::add(
                    a.clone_tree(),
                    Expr::neg(b.clone_tree()),
                ),
                Expr::neg(Expr::mul(
                    Expr::constant(2),
                    Expr::or(a.clone_tree(), Expr::not(b.clone_tree())),
                )),
            ),
            Expr::neg(Expr::constant(2)),
        );
        let cand = match_xor_via_ornot_flat(&lhs, 64).expect("match");
        assert!(matches!(cand.kind, Kind::Xor));
    }

    #[test]
    fn no_match_on_plain_add() {
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        assert!(try_match_all(&e, 64).is_empty());
    }
}
