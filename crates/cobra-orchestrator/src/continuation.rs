//! Deferred-recombine payloads carried by competition groups while a
//!
//! Each variant describes how a future child-solve result should be
//! composed back into its parent, carrying only the minimal data
//! required to reconstruct the parent context at resolution time.

use cobra_core::evaluator::Evaluator;
use cobra_core::expr::Expr;
use cobra_core::expr_cost::ExprCost;

use crate::enums::RemainderOrigin;
use crate::stubs::{ExtractOp, GateKind};

pub type GroupId = u32;

pub type JoinId = u32;

// ----- Bitwise decompose continuation -----

#[derive(Clone, Debug)]
pub struct BitwiseComposeCont {
    pub var_k: u32,
    pub gate: GateKind,
    pub add_coeff: u64,
    pub active_context_indices: Vec<u32>,
    pub parent_group_id: GroupId,
    pub parent_eval: Option<Evaluator>,
    pub parent_signature: Vec<u64>,
    pub parent_real_vars: Vec<String>,
    pub parent_original_indices: Vec<u32>,
    pub parent_num_vars: u32,
    pub parent_needs_original_space_verification: bool,
}

impl Default for BitwiseComposeCont {
    fn default() -> Self {
        Self {
            var_k: 0,
            gate: GateKind::And,
            add_coeff: 0,
            active_context_indices: Vec::new(),
            parent_group_id: 0,
            parent_eval: None,
            parent_signature: Vec::new(),
            parent_real_vars: Vec::new(),
            parent_original_indices: Vec::new(),
            parent_num_vars: 0,
            parent_needs_original_space_verification: true,
        }
    }
}

// ----- Hybrid decompose continuation -----

#[derive(Clone, Debug)]
pub struct HybridComposeCont {
    pub var_k: u32,
    pub op: ExtractOp,
    pub parent_group_id: GroupId,
    pub parent_eval: Option<Evaluator>,
    pub parent_signature: Vec<u64>,
    pub parent_real_vars: Vec<String>,
    pub parent_original_indices: Vec<u32>,
    pub parent_num_vars: u32,
    pub parent_needs_original_space_verification: bool,
}

impl Default for HybridComposeCont {
    fn default() -> Self {
        Self {
            var_k: 0,
            op: ExtractOp::Xor,
            parent_group_id: 0,
            parent_eval: None,
            parent_signature: Vec::new(),
            parent_real_vars: Vec::new(),
            parent_original_indices: Vec::new(),
            parent_num_vars: 0,
            parent_needs_original_space_verification: true,
        }
    }
}

// ----- Remainder recombine continuation -----

#[derive(Clone, Debug)]
pub struct RemainderRecombineCont {
    pub prefix_expr: Box<Expr>,
    pub origin: RemainderOrigin,
    pub remainder_eval: Evaluator,
    pub source_sig: Vec<u64>,
    pub remainder_support: Vec<u32>,
    pub prefix_degree: u8,
    pub parent_group_id: Option<GroupId>,
    /// Target-local context for verification. When `target_vars` is
    /// non-empty, recombination verifies against `target_eval` in the
    /// target variable space instead of `ctx.original_vars`.
    pub target_eval: Evaluator,
    pub target_vars: Vec<String>,
}

// ----- Structural-rewrite continuations -----

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum OperandRole {
    #[default]
    Lhs,
    Rhs,
}

#[derive(Copy, Clone, Debug)]
pub struct OperandRewriteCont {
    pub join_id: JoinId,
    pub role: OperandRole,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum FactorRole {
    #[default]
    X,
    Y,
}

#[derive(Copy, Clone, Debug)]
pub struct ProductCollapseCont {
    pub join_id: JoinId,
    pub role: FactorRole,
}

// ----- Lifting -----

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum LiftedValueKind {
    #[default]
    ArithmeticAtom,
    RepeatedSubexpression,
}

#[derive(Clone, Debug)]
pub struct LiftedBinding {
    pub kind: LiftedValueKind,
    pub outer_var_index: u32,
    pub subtree: Box<Expr>,
    pub structural_hash: u64,
    pub original_support: Vec<u32>,
}

#[derive(Clone, Debug, Default)]
pub struct LiftedSubstituteCont {
    pub bindings: Vec<LiftedBinding>,
    pub outer_vars: Vec<String>,
    pub original_var_count: u32,
    pub original_eval: Option<Evaluator>,
    pub original_vars: Vec<String>,
    pub source_sig: Vec<u64>,
}

// ----- Umbrella enum -----

/// `ContinuationData = std::variant<monostate, ...>` — the `None` arm
/// (here just `Default::default()` → `None`) replaces `std::monostate`.
#[derive(Clone, Debug, Default)]
pub enum ContinuationData {
    #[default]
    None,
    BitwiseCompose(Box<BitwiseComposeCont>),
    HybridCompose(Box<HybridComposeCont>),
    RemainderRecombine(Box<RemainderRecombineCont>),
    OperandRewrite(OperandRewriteCont),
    ProductCollapse(ProductCollapseCont),
    LiftedSubstitute(Box<LiftedSubstituteCont>),
}

/// inheritance is performed across continuation boundaries yet.
#[inline]
#[must_use]
pub fn project_baseline_for_child(
    _parent_baseline: Option<ExprCost>,
    _continuation: &ContinuationData,
) -> Option<ExprCost> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn continuation_data_defaults_to_none() {
        let c = ContinuationData::default();
        assert!(matches!(c, ContinuationData::None));
    }

    #[test]
    fn operand_and_factor_roles_have_defaults() {
        assert_eq!(OperandRole::default(), OperandRole::Lhs);
        assert_eq!(FactorRole::default(), FactorRole::X);
    }

    #[test]
    fn project_baseline_always_none_for_now() {
        let baseline = ExprCost {
            weighted_size: 10,
            nonlinear_mul_count: 0,
            max_depth: 3,
        };
        assert!(project_baseline_for_child(Some(baseline), &ContinuationData::None).is_none());
        assert!(project_baseline_for_child(None, &ContinuationData::None).is_none());
    }
}
