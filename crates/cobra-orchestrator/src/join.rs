//! `lib/core/JoinState.{h,cpp}`.

use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::ExprCost;

use crate::competition::{CandidateRecord, JoinId};
use crate::context::expr_identity_hash;
use crate::continuation::GroupId;
use crate::enums::PassId;

/// Tracks a two-operand rewrite (`lhs op rhs`) where each side spawns an
#[derive(Clone, Debug)]
pub struct OperandJoinState {
    pub lhs_winner: Option<CandidateRecord>,
    pub rhs_winner: Option<CandidateRecord>,
    pub lhs_resolved: bool,
    pub rhs_resolved: bool,
    pub full_ast: Box<Expr>,
    /// while both sides are being solved).
    pub original_mul: Box<Expr>,
    /// Hash of the target `Mul` for splicing back into `full_ast`.
    pub target_hash: u64,
    pub baseline_cost: ExprCost,
    pub vars: Vec<String>,
    pub parent_group_id: Option<GroupId>,
    pub has_solve_ctx: bool,
    pub solve_ctx_vars: Vec<String>,
    pub solve_ctx_evaluator: Option<Evaluator>,
    pub solve_ctx_input_sig: Vec<u64>,
    pub bitwidth: u32,
    pub parent_depth: u32,
    pub rewrite_gen: u32,
    pub parent_history: Vec<PassId>,
}

/// Two-factor product identity collapse. Both `x` and `y` spawn child
/// solves; on completion the join splices the collapsed product back
/// into the full AST by hash.
#[derive(Clone, Debug)]
pub struct ProductJoinState {
    pub x_winner: Option<CandidateRecord>,
    pub y_winner: Option<CandidateRecord>,
    pub x_resolved: bool,
    pub y_resolved: bool,
    pub original_expr: Box<Expr>,
    pub baseline_cost: ExprCost,
    pub vars: Vec<String>,
    pub parent_group_id: Option<GroupId>,
    pub has_solve_ctx: bool,
    pub solve_ctx_vars: Vec<String>,
    pub solve_ctx_evaluator: Option<Evaluator>,
    pub solve_ctx_input_sig: Vec<u64>,
    pub bitwidth: u32,
    pub parent_depth: u32,
    pub rewrite_gen: u32,
    pub parent_history: Vec<PassId>,
    /// Full AST for replacement splicing.
    pub full_ast: Box<Expr>,
    pub target_hash: u64,
}

#[derive(Clone, Debug)]
pub enum JoinState {
    Operand(Box<OperandJoinState>),
    Product(Box<ProductJoinState>),
}

/// `absl::flat_hash_map<JoinId, JoinState>`.
pub type JoinMap = std::collections::HashMap<JoinId, JoinState, ahash::RandomState>;

// ---------------------------------------------------------------
// ---------------------------------------------------------------

/// `CreateJoin`.
pub fn create_join(joins: &mut JoinMap, next_id: &mut JoinId, state: JoinState) -> JoinId {
    let id = *next_id;
    *next_id = next_id.wrapping_add(1);
    joins.insert(id, state);
    id
}

/// Walk `root` and replace the first subtree whose identity hash (via
/// [`expr_identity_hash`]) equals `target_hash`. The replacement is
/// consumed on match; otherwise it is left untouched.
///
/// Returns the rebuilt tree plus a `replaced` flag indicating whether
#[allow(clippy::unnecessary_box_returns)]
pub fn replace_by_hash(
    root: Box<Expr>,
    target_hash: u64,
    replacement: &mut Option<Box<Expr>>,
) -> (Box<Expr>, bool) {
    // Precompute structural hashes for every node in a single postorder
    // pass, keyed by raw pointer. `root` is owned and no child is moved
    // until we match, so these pointers remain valid for the walk below.
    let mut hashes: std::collections::HashMap<*const Expr, u64> =
        std::collections::HashMap::with_capacity(16);
    precompute_hashes(&root, &mut hashes);
    let mut replaced = false;
    let out = replace_by_hash_rec(root, target_hash, replacement, &mut replaced, &hashes);
    (out, replaced)
}

fn precompute_hashes(
    node: &Expr,
    out: &mut std::collections::HashMap<*const Expr, u64>,
) {
    for child in &node.children {
        precompute_hashes(child, out);
    }
    out.insert(node as *const Expr, expr_identity_hash(node));
}

#[allow(clippy::unnecessary_box_returns)]
fn replace_by_hash_rec(
    root: Box<Expr>,
    target_hash: u64,
    replacement: &mut Option<Box<Expr>>,
    replaced: &mut bool,
    hashes: &std::collections::HashMap<*const Expr, u64>,
) -> Box<Expr> {
    if *replaced {
        return root;
    }
    let this_hash = hashes
        .get(&(root.as_ref() as *const Expr))
        .copied()
        .unwrap_or_else(|| expr_identity_hash(&root));
    if this_hash == target_hash {
        if let Some(new_root) = replacement.take() {
            *replaced = true;
            return new_root;
        }
    }
    let mut root = root;
    for i in 0..root.children.len() {
        let child = std::mem::replace(&mut root.children[i], Expr::constant(0));
        let rebuilt = replace_by_hash_rec(child, target_hash, replacement, replaced, hashes);
        root.children[i] = rebuilt;
        if *replaced {
            break;
        }
    }
    root
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_join_allocates_sequential_ids() {
        let mut joins = JoinMap::with_hasher(crate::context::determinism_seeds_ahash());
        let mut next = 0u32;

        let mk_state = || {
            JoinState::Operand(Box::new(OperandJoinState {
                lhs_winner: None,
                rhs_winner: None,
                lhs_resolved: false,
                rhs_resolved: false,
                full_ast: Expr::variable(0),
                original_mul: Expr::variable(0),
                target_hash: 0,
                baseline_cost: ExprCost::default(),
                vars: vec![],
                parent_group_id: None,
                has_solve_ctx: false,
                solve_ctx_vars: vec![],
                solve_ctx_evaluator: None,
                solve_ctx_input_sig: vec![],
                bitwidth: 64,
                parent_depth: 0,
                rewrite_gen: 0,
                parent_history: vec![],
            }))
        };
        assert_eq!(create_join(&mut joins, &mut next, mk_state()), 0);
        assert_eq!(create_join(&mut joins, &mut next, mk_state()), 1);
        assert_eq!(next, 2);
        assert_eq!(joins.len(), 2);
    }

    #[test]
    fn replace_by_hash_swaps_first_match() {
        // Tree: (a + b) * c
        let a = Expr::variable(0);
        let b = Expr::variable(1);
        let c = Expr::variable(2);
        let add = Expr::add(a.clone_tree(), b.clone_tree());
        let add_hash = expr_identity_hash(&add);
        let tree = Expr::mul(add, c);

        let mut replacement = Some(Expr::constant(42));
        let (new_tree, replaced) = replace_by_hash(tree, add_hash, &mut replacement);
        assert!(replaced);
        assert!(replacement.is_none()); // consumed
                                        // new_tree should be Mul(Constant(42), c)
        assert!(matches!(new_tree.kind, cobra_core::expr::Kind::Mul));
        assert!(matches!(
            new_tree.children[0].kind,
            cobra_core::expr::Kind::Constant(42)
        ));
    }

    #[test]
    fn replace_by_hash_noop_on_miss() {
        let tree = Expr::add(Expr::variable(0), Expr::variable(1));
        let bogus_hash: u64 = 0xDEAD_BEEF_DEAD_BEEF;
        let mut replacement = Some(Expr::constant(7));
        let (out, replaced) = replace_by_hash(tree, bogus_hash, &mut replacement);
        assert!(!replaced);
        assert!(replacement.is_some()); // untouched
                                        // Structure preserved
        assert!(matches!(out.kind, cobra_core::expr::Kind::Add));
    }

    #[test]
    fn replace_by_hash_replaces_at_root() {
        let tree = Expr::variable(0);
        let target_hash = expr_identity_hash(&tree);
        let mut replacement = Some(Expr::constant(99));
        let (out, replaced) = replace_by_hash(tree, target_hash, &mut replacement);
        assert!(replaced);
        assert!(matches!(out.kind, cobra_core::expr::Kind::Constant(99)));
    }

    #[test]
    fn join_state_variants_carry_their_payload_shape() {
        let op = OperandJoinState {
            lhs_winner: None,
            rhs_winner: None,
            lhs_resolved: false,
            rhs_resolved: false,
            full_ast: Expr::variable(0),
            original_mul: Expr::variable(0),
            target_hash: 0,
            baseline_cost: ExprCost::default(),
            vars: vec![],
            parent_group_id: None,
            has_solve_ctx: false,
            solve_ctx_vars: vec![],
            solve_ctx_evaluator: None,
            solve_ctx_input_sig: vec![],
            bitwidth: 64,
            parent_depth: 0,
            rewrite_gen: 0,
            parent_history: vec![],
        };
        let js = JoinState::Operand(Box::new(op));
        assert!(matches!(js, JoinState::Operand(_)));
    }
}
