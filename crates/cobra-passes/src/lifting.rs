//! Lifting helpers shared by `LiftArithmeticAtoms` and
//! `LiftRepeatedSubexpressions`.
//!
//! Both passes find candidate subtrees in a `FoldedAst`, replace them
//! with virtual variables, and emit a `LiftedSkeletonPayload` so the
//! outer (now smaller) problem is re-solved by the rest of the
//! pipeline. The payload carries `LiftedBinding` records so
//! `ResolveCompetition` can substitute the original subtrees back in
//! once the outer winner is known.

use std::collections::HashMap;

use cobra_core::evaluate_boolean_signature;
use cobra_core::expr::{render, Expr, Kind};
use cobra_core::expr_cost::compute_cost;
use cobra_core::expr_utils::has_var_dep;

use cobra_orchestrator::{expr_identity_hash, LiftedBinding, LiftedValueKind};

#[must_use]
pub fn is_bitwise_kind(k: &Kind) -> bool {
    matches!(k, Kind::And | Kind::Or | Kind::Xor | Kind::Not)
}

#[must_use]
pub fn is_pure_arithmetic(e: &Expr) -> bool {
    match e.kind {
        Kind::Constant(_) | Kind::Variable(_) => true,
        Kind::Add | Kind::Mul | Kind::Neg => e.children.iter().all(|c| is_pure_arithmetic(c)),
        _ => false,
    }
}

#[must_use]
pub fn count_nodes(e: &Expr) -> u32 {
    let mut n = 1u32;
    for c in &e.children {
        n += count_nodes(c);
    }
    n
}

#[derive(Clone)]
pub struct LiftCandidate<'a> {
    pub subtree: &'a Expr,
    pub hash: u64,
    pub rendered: String,
}

/// Walks `node` and pushes every pure-arithmetic, var-dependent,
/// non-variable subtree that sits directly under a bitwise parent.
pub fn collect_liftable_atoms<'a>(
    node: &'a Expr,
    parent_is_bitwise: bool,
    vars: &[String],
    bitwidth: u32,
    out: &mut Vec<LiftCandidate<'a>>,
) {
    if parent_is_bitwise
        && is_pure_arithmetic(node)
        && has_var_dep(node)
        && !matches!(node.kind, Kind::Variable(_))
    {
        let hash = expr_identity_hash(node);
        let rendered = render(node, vars, bitwidth);
        out.push(LiftCandidate {
            subtree: node,
            hash,
            rendered,
        });
        return;
    }
    let current_is_bitwise = is_bitwise_kind(&node.kind);
    for child in &node.children {
        collect_liftable_atoms(child, current_is_bitwise, vars, bitwidth, out);
    }
}

#[derive(Clone)]
pub struct DeduplicatedAtom<'a> {
    pub subtree: &'a Expr,
    pub hash: u64,
    pub rendered: String,
    pub virtual_index: u32,
}

#[must_use]
pub fn deduplicate_atoms<'a>(
    candidates: &[LiftCandidate<'a>],
    first_virtual_index: u32,
) -> Vec<DeduplicatedAtom<'a>> {
    let mut result: Vec<DeduplicatedAtom<'a>> = Vec::new();
    let mut by_hash: HashMap<u64, Vec<usize>> = HashMap::new();
    for cand in candidates {
        let mut found = false;
        if let Some(idxs) = by_hash.get(&cand.hash) {
            for &idx in idxs {
                if result[idx].rendered == cand.rendered {
                    found = true;
                    break;
                }
            }
        }
        if !found {
            let vi = first_virtual_index + result.len() as u32;
            by_hash.entry(cand.hash).or_default().push(result.len());
            result.push(DeduplicatedAtom {
                subtree: cand.subtree,
                hash: cand.hash,
                rendered: cand.rendered.clone(),
                virtual_index: vi,
            });
        }
    }
    result
}

#[must_use]
pub fn allocate_fresh_virtual_names(
    existing: &[String],
    prefix: &str,
    count: usize,
) -> Vec<String> {
    let mut used: std::collections::HashSet<String> = existing.iter().cloned().collect();
    let mut out = Vec::with_capacity(count);
    let mut next: usize = 0;
    while out.len() < count {
        let candidate = format!("{prefix}{next}");
        next += 1;
        if used.insert(candidate.clone()) {
            out.push(candidate);
        }
    }
    out
}

fn build_atom_index(atoms: &[DeduplicatedAtom<'_>]) -> HashMap<u64, Vec<usize>> {
    let mut idx: HashMap<u64, Vec<usize>> = HashMap::with_capacity(atoms.len());
    for (i, atom) in atoms.iter().enumerate() {
        idx.entry(atom.hash).or_default().push(i);
    }
    idx
}

fn find_virtual_index(
    node: &Expr,
    atoms: &[DeduplicatedAtom<'_>],
    index: &HashMap<u64, Vec<usize>>,
    vars: &[String],
    bitwidth: u32,
) -> Option<u32> {
    let h = expr_identity_hash(node);
    let bucket = index.get(&h)?;
    // Fast path: single-entry bucket (the common case). Trust the
    // structural hash to identify the atom without re-rendering.
    if bucket.len() == 1 {
        return Some(atoms[bucket[0]].virtual_index);
    }
    let rendered = render(node, vars, bitwidth);
    for &i in bucket {
        if atoms[i].rendered == rendered {
            return Some(atoms[i].virtual_index);
        }
    }
    None
}

#[must_use]
pub fn replace_atoms_with_virtual(
    node: &Expr,
    parent_is_bitwise: bool,
    atoms: &[DeduplicatedAtom<'_>],
    vars: &[String],
    bitwidth: u32,
) -> Box<Expr> {
    let index = build_atom_index(atoms);
    replace_atoms_with_virtual_inner(node, parent_is_bitwise, atoms, &index, vars, bitwidth)
}

fn replace_atoms_with_virtual_inner(
    node: &Expr,
    parent_is_bitwise: bool,
    atoms: &[DeduplicatedAtom<'_>],
    index: &HashMap<u64, Vec<usize>>,
    vars: &[String],
    bitwidth: u32,
) -> Box<Expr> {
    if parent_is_bitwise
        && is_pure_arithmetic(node)
        && has_var_dep(node)
        && !matches!(node.kind, Kind::Variable(_))
    {
        if let Some(vi) = find_virtual_index(node, atoms, index, vars, bitwidth) {
            return Expr::variable(vi);
        }
    }
    let current_is_bitwise = is_bitwise_kind(&node.kind);
    let mut result = node.clone_tree();
    for i in 0..result.children.len() {
        let child = std::mem::replace(&mut result.children[i], Expr::constant(0));
        result.children[i] = replace_atoms_with_virtual_inner(
            &child,
            current_is_bitwise,
            atoms,
            index,
            vars,
            bitwidth,
        );
    }
    result
}

#[must_use]
pub fn replace_repeats_with_virtual(
    node: &Expr,
    atoms: &[DeduplicatedAtom<'_>],
    vars: &[String],
    bitwidth: u32,
) -> Box<Expr> {
    let index = build_atom_index(atoms);
    replace_repeats_with_virtual_inner(node, atoms, &index, vars, bitwidth)
}

fn replace_repeats_with_virtual_inner(
    node: &Expr,
    atoms: &[DeduplicatedAtom<'_>],
    index: &HashMap<u64, Vec<usize>>,
    vars: &[String],
    bitwidth: u32,
) -> Box<Expr> {
    if !matches!(node.kind, Kind::Constant(_) | Kind::Variable(_)) {
        let h = expr_identity_hash(node);
        if let Some(bucket) = index.get(&h) {
            if bucket.len() == 1 {
                return Expr::variable(atoms[bucket[0]].virtual_index);
            }
            let rendered = render(node, vars, bitwidth);
            for &i in bucket {
                if atoms[i].rendered == rendered {
                    return Expr::variable(atoms[i].virtual_index);
                }
            }
        }
    }
    let mut result = node.clone_tree();
    for i in 0..result.children.len() {
        let child = std::mem::replace(&mut result.children[i], Expr::constant(0));
        result.children[i] =
            replace_repeats_with_virtual_inner(&child, atoms, index, vars, bitwidth);
    }
    result
}

pub fn collect_var_support(e: &Expr, out: &mut Vec<u32>) {
    if let Kind::Variable(i) = e.kind {
        if !out.contains(&i) {
            out.push(i);
        }
        return;
    }
    for c in &e.children {
        collect_var_support(c, out);
    }
}

#[must_use]
pub fn make_binding(atom: &DeduplicatedAtom<'_>, kind: LiftedValueKind) -> LiftedBinding {
    let mut support: Vec<u32> = Vec::new();
    collect_var_support(atom.subtree, &mut support);
    LiftedBinding {
        kind,
        outer_var_index: atom.virtual_index,
        subtree: atom.subtree.clone_tree(),
        structural_hash: atom.hash,
        original_support: support,
    }
}

// ---------------------------------------------------------------
// Repeated-subexpression discovery.
// ---------------------------------------------------------------

pub const MIN_REPEAT_SIZE: u32 = 4;
pub const MAX_LIFTABLE_NODES: u32 = 50_000;

#[derive(Clone)]
pub struct RepeatEntry<'a> {
    pub hash: u64,
    pub first_occurrence: &'a Expr,
    pub count: u32,
    pub size: u32,
    pub first_preorder: u32,
}

#[allow(clippy::implicit_hasher)]
pub fn collect_non_leaf_subtrees<'a>(
    node: &'a Expr,
    preorder_counter: &mut u32,
    by_hash: &mut HashMap<u64, Vec<usize>>,
    entries: &mut Vec<RepeatEntry<'a>>,
) -> u32 {
    // Single postorder pass: compute subtree size bottom-up and
    // dedup non-leaf entries by structural hash only. The hash uses
    // a static RandomState, so hash-equal subtrees are treated as
    // equivalent (collision probability 2^-64 is accepted — the
    // codebase already relies on hash-only identity elsewhere).
    let my_order = *preorder_counter;
    *preorder_counter += 1;
    let is_leaf = matches!(node.kind, Kind::Constant(_) | Kind::Variable(_));
    let mut size: u32 = 1;
    for child in &node.children {
        size = size.saturating_add(collect_non_leaf_subtrees(
            child,
            preorder_counter,
            by_hash,
            entries,
        ));
    }
    if !is_leaf {
        let hash = expr_identity_hash(node);
        if let Some(idxs) = by_hash.get(&hash) {
            if let Some(&idx) = idxs.first() {
                entries[idx].count += 1;
                return size;
            }
        }
        by_hash.entry(hash).or_default().push(entries.len());
        entries.push(RepeatEntry {
            hash,
            first_occurrence: node,
            count: 1,
            size,
            first_preorder: my_order,
        });
    }
    size
}

#[must_use]
pub fn is_ancestor_of(ancestor: &Expr, descendant: &Expr) -> bool {
    if std::ptr::eq(ancestor, descendant) {
        return true;
    }
    for c in &ancestor.children {
        if is_ancestor_of(c, descendant) {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------
// Cost helpers re-exported for the pass bodies.
// ---------------------------------------------------------------

#[must_use]
pub fn boolean_signature(expr: &Expr, num_vars: u32, bitwidth: u32) -> Vec<u64> {
    evaluate_boolean_signature(expr, num_vars, bitwidth)
}

#[must_use]
pub fn baseline_cost(expr: &Expr) -> cobra_core::expr_cost::ExprCost {
    compute_cost(expr).cost
}
