//! Lean certificate data model.
//!
//! This module intentionally contains only stable, serializable-by-caller
//! data shapes. It does not invoke Lean; callers can emit these certificates
//! alongside candidate expressions and an external checker can replay them
//! against the theorem pack in `formal/lean`.

use cobra_core::expr::Expr;
use cobra_core::expr::Kind;

/// Theorem identifiers exported by `formal/lean/Cobra/Core.lean`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum LeanTheorem {
    CompileSound,
    ContextPreservesSemanticEquivalence,
    RewriteStepSound,
    ChainSound,
    BnotEqNegAddMask64,
    BnotEqNegAddAllOnes64,
    XorEqAddSubTwoMulAnd64,
    OrSubAndEqXor64,
    AndOrSumEqAdd64,
    TwoMulAndOrSumEqTwoMulAdd64,
    NotOrSubNotEqAnd64,
    NotOrAddSelfAddOneEqAnd64,
    XorViaOrNot64,
    AddComm64,
    AddAssoc64,
    MulComm64,
    MulAssoc64,
    MulAdd64,
    AddMul64,
    AddZero64,
    MulZero64,
    MulOne64,
    ZeroAdd64,
    ZeroMul64,
    OneMul64,
    NegNeg64,
    NotNot64,
    AndComm64,
    OrComm64,
    XorComm64,
    AndSelf64,
    OrSelf64,
    XorSelf64,
    XorZero64,
    ZeroXor64,
    AndZero64,
    Const3And1_64,
    ZeroAnd64,
    OrZero64,
    ZeroOr64,
    AndAllOnes64,
    AllOnesAnd64,
    OrAllOnes64,
    AllOnesOr64,
    DemorganNotAnd64,
    DemorganOrNotNot64,
    DemorganNotAndNotNot64,
    DemorganNotOr64,
    DemorganNotOrNotNot64,
    ShrZero64,
}

impl LeanTheorem {
    pub const ALL: &'static [Self] = &[
        Self::CompileSound,
        Self::ContextPreservesSemanticEquivalence,
        Self::RewriteStepSound,
        Self::ChainSound,
        Self::BnotEqNegAddMask64,
        Self::BnotEqNegAddAllOnes64,
        Self::XorEqAddSubTwoMulAnd64,
        Self::OrSubAndEqXor64,
        Self::AndOrSumEqAdd64,
        Self::TwoMulAndOrSumEqTwoMulAdd64,
        Self::NotOrSubNotEqAnd64,
        Self::NotOrAddSelfAddOneEqAnd64,
        Self::XorViaOrNot64,
        Self::AddComm64,
        Self::AddAssoc64,
        Self::MulComm64,
        Self::MulAssoc64,
        Self::MulAdd64,
        Self::AddMul64,
        Self::AddZero64,
        Self::MulZero64,
        Self::MulOne64,
        Self::ZeroAdd64,
        Self::ZeroMul64,
        Self::OneMul64,
        Self::NegNeg64,
        Self::NotNot64,
        Self::AndComm64,
        Self::OrComm64,
        Self::XorComm64,
        Self::AndSelf64,
        Self::OrSelf64,
        Self::XorSelf64,
        Self::XorZero64,
        Self::ZeroXor64,
        Self::AndZero64,
        Self::Const3And1_64,
        Self::ZeroAnd64,
        Self::OrZero64,
        Self::ZeroOr64,
        Self::AndAllOnes64,
        Self::AllOnesAnd64,
        Self::OrAllOnes64,
        Self::AllOnesOr64,
        Self::DemorganNotAnd64,
        Self::DemorganOrNotNot64,
        Self::DemorganNotAndNotNot64,
        Self::DemorganNotOr64,
        Self::DemorganNotOrNotNot64,
        Self::ShrZero64,
    ];

    pub const RECOGNIZED_REWRITE_64: &'static [Self] = &[
        Self::XorEqAddSubTwoMulAnd64,
        Self::OrSubAndEqXor64,
        Self::AndOrSumEqAdd64,
        Self::TwoMulAndOrSumEqTwoMulAdd64,
        Self::NotOrAddSelfAddOneEqAnd64,
        Self::XorViaOrNot64,
        Self::NotOrSubNotEqAnd64,
        Self::AddZero64,
        Self::MulZero64,
        Self::MulOne64,
        Self::ZeroAdd64,
        Self::ZeroMul64,
        Self::OneMul64,
        Self::NegNeg64,
        Self::NotNot64,
        Self::AndSelf64,
        Self::OrSelf64,
        Self::XorSelf64,
        Self::XorZero64,
        Self::ZeroXor64,
        Self::AndZero64,
        Self::Const3And1_64,
        Self::ZeroAnd64,
        Self::OrZero64,
        Self::ZeroOr64,
        Self::AndAllOnes64,
        Self::AllOnesAnd64,
        Self::OrAllOnes64,
        Self::AllOnesOr64,
        Self::DemorganNotAnd64,
        Self::DemorganOrNotNot64,
        Self::DemorganNotAndNotNot64,
        Self::DemorganNotOr64,
        Self::DemorganNotOrNotNot64,
        Self::BnotEqNegAddAllOnes64,
        Self::ShrZero64,
    ];

    #[must_use]
    pub const fn lean_name(self) -> &'static str {
        match self {
            Self::CompileSound => "Cobra.Expr.compile_sound",
            Self::ContextPreservesSemanticEquivalence => "Cobra.Ctx.plug_preserves_sem_eq",
            Self::RewriteStepSound => "Cobra.RewriteStep.sound",
            Self::ChainSound => "Cobra.Chain.sound",
            Self::BnotEqNegAddMask64 => "Cobra.bnot_eq_neg_add_mask_64",
            Self::BnotEqNegAddAllOnes64 => "Cobra.bnot_eq_neg_add_all_ones_64",
            Self::XorEqAddSubTwoMulAnd64 => "Cobra.xor_eq_add_sub_two_mul_and_64",
            Self::OrSubAndEqXor64 => "Cobra.or_sub_and_eq_xor_64",
            Self::AndOrSumEqAdd64 => "Cobra.and_or_sum_eq_add_64",
            Self::TwoMulAndOrSumEqTwoMulAdd64 => "Cobra.two_mul_and_or_sum_eq_two_mul_add_64",
            Self::NotOrSubNotEqAnd64 => "Cobra.not_or_sub_not_eq_and_64",
            Self::NotOrAddSelfAddOneEqAnd64 => "Cobra.not_or_add_self_add_one_eq_and_64",
            Self::XorViaOrNot64 => "Cobra.xor_via_or_not_64",
            Self::AddComm64 => "Cobra.add_comm_64",
            Self::AddAssoc64 => "Cobra.add_assoc_64",
            Self::MulComm64 => "Cobra.mul_comm_64",
            Self::MulAssoc64 => "Cobra.mul_assoc_64",
            Self::MulAdd64 => "Cobra.mul_add_64",
            Self::AddMul64 => "Cobra.add_mul_64",
            Self::AddZero64 => "Cobra.add_zero_64",
            Self::MulZero64 => "Cobra.mul_zero_64",
            Self::MulOne64 => "Cobra.mul_one_64",
            Self::ZeroAdd64 => "Cobra.zero_add_64",
            Self::ZeroMul64 => "Cobra.zero_mul_64",
            Self::OneMul64 => "Cobra.one_mul_64",
            Self::NegNeg64 => "Cobra.neg_neg_64",
            Self::NotNot64 => "Cobra.not_not_64",
            Self::AndComm64 => "Cobra.and_comm_64",
            Self::OrComm64 => "Cobra.or_comm_64",
            Self::XorComm64 => "Cobra.xor_comm_64",
            Self::AndSelf64 => "Cobra.and_self_64",
            Self::OrSelf64 => "Cobra.or_self_64",
            Self::XorSelf64 => "Cobra.xor_self_64",
            Self::XorZero64 => "Cobra.xor_zero_64",
            Self::ZeroXor64 => "Cobra.zero_xor_64",
            Self::AndZero64 => "Cobra.and_zero_64",
            Self::Const3And1_64 => "Cobra.const_3_and_1_64",
            Self::ZeroAnd64 => "Cobra.zero_and_64",
            Self::OrZero64 => "Cobra.or_zero_64",
            Self::ZeroOr64 => "Cobra.zero_or_64",
            Self::AndAllOnes64 => "Cobra.and_all_ones_64",
            Self::AllOnesAnd64 => "Cobra.all_ones_and_64",
            Self::OrAllOnes64 => "Cobra.or_all_ones_64",
            Self::AllOnesOr64 => "Cobra.all_ones_or_64",
            Self::DemorganNotAnd64 => "Cobra.demorgan_not_and_64",
            Self::DemorganOrNotNot64 => "Cobra.demorgan_or_not_not_64",
            Self::DemorganNotAndNotNot64 => "Cobra.demorgan_not_and_not_not_64",
            Self::DemorganNotOr64 => "Cobra.demorgan_not_or_64",
            Self::DemorganNotOrNotNot64 => "Cobra.demorgan_not_or_not_not_64",
            Self::ShrZero64 => "Cobra.shr_zero_64",
        }
    }
}

/// Child-index path from a certificate root expression to the rewritten node.
/// The empty path denotes the root.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ExprPath(pub Vec<u8>);

/// Generator-friendly expression context frame. Frames are ordered from the
/// rewrite site outward, so applying them left-to-right rebuilds the whole
/// expression around the local before/after pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextFrame {
    AddL { rhs: Box<Expr> },
    AddR { lhs: Box<Expr> },
    MulL { rhs: Box<Expr> },
    MulR { lhs: Box<Expr> },
    AndL { rhs: Box<Expr> },
    AndR { lhs: Box<Expr> },
    OrL { rhs: Box<Expr> },
    OrR { lhs: Box<Expr> },
    XorL { rhs: Box<Expr> },
    XorR { lhs: Box<Expr> },
    Not,
    Neg,
    Shr { amount: u32 },
}

/// Explicit context payload corresponding to `Cobra.Ctx`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExprContext {
    pub frames: Vec<ContextFrame>,
}

impl ExprContext {
    #[must_use]
    pub fn plug(&self, mut expr: Box<Expr>) -> Box<Expr> {
        for frame in &self.frames {
            expr = frame.plug(expr);
        }
        expr
    }
}

impl ContextFrame {
    #[must_use]
    pub fn plug(&self, expr: Box<Expr>) -> Box<Expr> {
        match self {
            Self::AddL { rhs } => Expr::add(expr, rhs.clone_tree()),
            Self::AddR { lhs } => Expr::add(lhs.clone_tree(), expr),
            Self::MulL { rhs } => Expr::mul(expr, rhs.clone_tree()),
            Self::MulR { lhs } => Expr::mul(lhs.clone_tree(), expr),
            Self::AndL { rhs } => Expr::and(expr, rhs.clone_tree()),
            Self::AndR { lhs } => Expr::and(lhs.clone_tree(), expr),
            Self::OrL { rhs } => Expr::or(expr, rhs.clone_tree()),
            Self::OrR { lhs } => Expr::or(lhs.clone_tree(), expr),
            Self::XorL { rhs } => Expr::xor(expr, rhs.clone_tree()),
            Self::XorR { lhs } => Expr::xor(lhs.clone_tree(), expr),
            Self::Not => Expr::not(expr),
            Self::Neg => Expr::neg(expr),
            Self::Shr { amount } => Expr::shr(expr, u64::from(*amount)),
        }
    }
}

#[must_use]
pub fn context_from_path(root: &Expr, path: &ExprPath) -> Option<(ExprContext, Box<Expr>)> {
    let mut current = root;
    let mut root_to_site = Vec::new();

    for &child_index in &path.0 {
        let index = usize::from(child_index);
        let frame = match &current.kind {
            cobra_core::expr::Kind::Add if current.children.len() == 2 => match index {
                0 => ContextFrame::AddL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::AddR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            cobra_core::expr::Kind::Mul if current.children.len() == 2 => match index {
                0 => ContextFrame::MulL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::MulR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            cobra_core::expr::Kind::And if current.children.len() == 2 => match index {
                0 => ContextFrame::AndL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::AndR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            cobra_core::expr::Kind::Or if current.children.len() == 2 => match index {
                0 => ContextFrame::OrL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::OrR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            cobra_core::expr::Kind::Xor if current.children.len() == 2 => match index {
                0 => ContextFrame::XorL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::XorR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            cobra_core::expr::Kind::Not if current.children.len() == 1 && index == 0 => {
                ContextFrame::Not
            }
            cobra_core::expr::Kind::Neg if current.children.len() == 1 && index == 0 => {
                ContextFrame::Neg
            }
            cobra_core::expr::Kind::Shr(amount) if current.children.len() == 1 && index == 0 => {
                ContextFrame::Shr { amount: *amount }
            }
            _ => return None,
        };
        root_to_site.push(frame);
        current = current.children.get(index)?;
    }

    root_to_site.reverse();
    Some((
        ExprContext {
            frames: root_to_site,
        },
        current.clone_tree(),
    ))
}

#[must_use]
pub fn identify_rewrite_theorem_64(before: &Expr, after: &Expr) -> Option<LeanTheorem> {
    use LeanTheorem as Thm;

    match &before.kind {
        Kind::Add if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if is_zero(rhs) && expr_eq(lhs, after) {
                return Some(Thm::AddZero64);
            }
            if is_zero(lhs) && expr_eq(rhs, after) {
                return Some(Thm::ZeroAdd64);
            }
            if let Some((or_node, and_node)) = add_with_neg_operands(before) {
                if let Some((a, b)) = same_or_and_operands(or_node, and_node) {
                    if is_xor_of(after, a, b) {
                        return Some(Thm::OrSubAndEqXor64);
                    }
                }
                if let Some((a, b)) = not_or_minus_not_operands(or_node, and_node) {
                    if is_and_of(after, a, b) {
                        return Some(Thm::NotOrSubNotEqAnd64);
                    }
                }
            }
            if let Some((a, b)) = and_or_sum_operands(lhs, rhs) {
                if is_add_of(after, a, b) {
                    return Some(Thm::AndOrSumEqAdd64);
                }
            }
            if let Some((a, b)) = scaled_and_or_sum_operands(lhs, rhs, 2) {
                if is_scaled_add_of(after, a, b, 2) {
                    return Some(Thm::TwoMulAndOrSumEqTwoMulAdd64);
                }
            }
            if let Some((a, b)) = not_or_add_self_add_one_operands(before) {
                if is_and_of(after, a, b) {
                    return Some(Thm::NotOrAddSelfAddOneEqAnd64);
                }
            }
            if let Some((a, b)) = xor_via_or_not_operands(before) {
                if is_xor_of(after, a, b) {
                    return Some(Thm::XorViaOrNot64);
                }
            }
        }
        Kind::Mul if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if is_zero(rhs) && is_zero(after) {
                return Some(Thm::MulZero64);
            }
            if is_zero(lhs) && is_zero(after) {
                return Some(Thm::ZeroMul64);
            }
            if is_one(rhs) && expr_eq(lhs, after) {
                return Some(Thm::MulOne64);
            }
            if is_one(lhs) && expr_eq(rhs, after) {
                return Some(Thm::OneMul64);
            }
        }
        Kind::And if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if expr_eq(lhs, rhs) && expr_eq(lhs, after) {
                return Some(Thm::AndSelf64);
            }
            if is_zero(rhs) && is_zero(after) {
                return Some(Thm::AndZero64);
            }
            if is_const_value(lhs, 3) && is_const_value(rhs, 1) && is_const_value(after, 1) {
                return Some(Thm::Const3And1_64);
            }
            if is_zero(lhs) && is_zero(after) {
                return Some(Thm::ZeroAnd64);
            }
            if is_all_ones(rhs) && expr_eq(lhs, after) {
                return Some(Thm::AndAllOnes64);
            }
            if is_all_ones(lhs) && expr_eq(rhs, after) {
                return Some(Thm::AllOnesAnd64);
            }
        }
        Kind::Or if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if expr_eq(lhs, rhs) && expr_eq(lhs, after) {
                return Some(Thm::OrSelf64);
            }
            if is_zero(rhs) && expr_eq(lhs, after) {
                return Some(Thm::OrZero64);
            }
            if is_zero(lhs) && expr_eq(rhs, after) {
                return Some(Thm::ZeroOr64);
            }
            if let Some((lhs, rhs)) = not_pair_operands(lhs, rhs) {
                if is_not_of_and(after, lhs, rhs) {
                    return Some(Thm::DemorganOrNotNot64);
                }
            }
            if is_all_ones(rhs) && is_all_ones(after) {
                return Some(Thm::OrAllOnes64);
            }
            if is_all_ones(lhs) && is_all_ones(after) {
                return Some(Thm::AllOnesOr64);
            }
        }
        Kind::Xor if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if is_xor_lowering_of(after, lhs, rhs) {
                return Some(Thm::XorEqAddSubTwoMulAnd64);
            }
            if expr_eq(lhs, rhs) && is_zero(after) {
                return Some(Thm::XorSelf64);
            }
            if is_zero(rhs) && expr_eq(lhs, after) {
                return Some(Thm::XorZero64);
            }
            if is_zero(lhs) && expr_eq(rhs, after) {
                return Some(Thm::ZeroXor64);
            }
        }
        Kind::Not if before.children.len() == 1 => {
            let child = &before.children[0];
            if matches!(child.kind, Kind::Not)
                && child.children.len() == 1
                && expr_eq(&child.children[0], after)
            {
                return Some(Thm::NotNot64);
            }
            if let Some((lhs, rhs, was_and)) = not_of_and_or(child) {
                if was_and && is_or_of_not_pair(after, lhs, rhs) {
                    return Some(Thm::DemorganNotAnd64);
                }
                if was_and {
                    if let Some((lhs, rhs)) = not_pair_operands(lhs, rhs) {
                        if is_or_of(after, lhs, rhs) {
                            return Some(Thm::DemorganNotAndNotNot64);
                        }
                    }
                }
                if !was_and && is_and_of_not_pair(after, lhs, rhs) {
                    return Some(Thm::DemorganNotOr64);
                }
                if !was_and {
                    if let Some((lhs, rhs)) = not_pair_operands(lhs, rhs) {
                        if is_and_of(after, lhs, rhs) {
                            return Some(Thm::DemorganNotOrNotNot64);
                        }
                    }
                }
            }
            if is_neg_add_all_ones_of(after, child) {
                return Some(Thm::BnotEqNegAddAllOnes64);
            }
        }
        Kind::Neg if before.children.len() == 1 => {
            let child = &before.children[0];
            if matches!(child.kind, Kind::Neg)
                && child.children.len() == 1
                && expr_eq(&child.children[0], after)
            {
                return Some(Thm::NegNeg64);
            }
        }
        Kind::Shr(0) if before.children.len() == 1 && expr_eq(&before.children[0], after) => {
            return Some(Thm::ShrZero64);
        }
        _ => {}
    }

    None
}

fn add_with_neg_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let lhs = &expr.children[0];
    let rhs = &expr.children[1];
    if matches!(rhs.kind, Kind::Neg) && rhs.children.len() == 1 {
        Some((lhs, &rhs.children[0]))
    } else if matches!(lhs.kind, Kind::Neg) && lhs.children.len() == 1 {
        Some((rhs, &lhs.children[0]))
    } else {
        None
    }
}

fn same_or_and_operands<'a>(or_node: &'a Expr, and_node: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    if !matches!(or_node.kind, Kind::Or) || !matches!(and_node.kind, Kind::And) {
        return None;
    }
    if or_node.children.len() != 2 || and_node.children.len() != 2 {
        return None;
    }
    let a = &or_node.children[0];
    let b = &or_node.children[1];
    let x = &and_node.children[0];
    let y = &and_node.children[1];
    if unordered_pair_eq(a, b, x, y) {
        Some((a, b))
    } else {
        None
    }
}

fn and_or_sum_operands<'a>(lhs: &'a Expr, rhs: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    if let Some((a, b)) = same_or_and_operands(lhs, rhs) {
        Some((a, b))
    } else {
        same_or_and_operands(rhs, lhs)
    }
}

fn scaled_and_or_sum_operands<'a>(
    lhs: &'a Expr,
    rhs: &'a Expr,
    coeff: u64,
) -> Option<(&'a Expr, &'a Expr)> {
    let lhs = scaled_child(lhs, coeff)?;
    let rhs = scaled_child(rhs, coeff)?;
    and_or_sum_operands(lhs, rhs)
}

fn scaled_child(expr: &Expr, coeff: u64) -> Option<&Expr> {
    if !matches!(expr.kind, Kind::Mul) || expr.children.len() != 2 {
        return None;
    }
    if is_const_value(&expr.children[0], coeff) {
        Some(&expr.children[1])
    } else if is_const_value(&expr.children[1], coeff) {
        Some(&expr.children[0])
    } else {
        None
    }
}

fn not_or_minus_not_operands<'a>(
    or_node: &'a Expr,
    not_node: &'a Expr,
) -> Option<(&'a Expr, &'a Expr)> {
    if !matches!(or_node.kind, Kind::Or)
        || or_node.children.len() != 2
        || !matches!(not_node.kind, Kind::Not)
        || not_node.children.len() != 1
    {
        return None;
    }
    let a = &not_node.children[0];
    let lhs = &or_node.children[0];
    let rhs = &or_node.children[1];
    if is_not_of(lhs, a) {
        Some((a, rhs))
    } else if is_not_of(rhs, a) {
        Some((a, lhs))
    } else {
        None
    }
}

struct SignedAddend<'a> {
    expr: &'a Expr,
    negated: bool,
}

fn flatten_signed_addends<'a>(expr: &'a Expr, negated: bool, out: &mut Vec<SignedAddend<'a>>) {
    match expr.kind {
        Kind::Add if expr.children.len() == 2 => {
            flatten_signed_addends(&expr.children[0], negated, out);
            flatten_signed_addends(&expr.children[1], negated, out);
        }
        Kind::Neg if expr.children.len() == 1 => {
            flatten_signed_addends(&expr.children[0], !negated, out);
        }
        _ => out.push(SignedAddend { expr, negated }),
    }
}

fn not_or_add_self_add_one_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let mut addends = Vec::new();
    flatten_signed_addends(expr, false, &mut addends);
    if addends.len() != 3 || addends.iter().any(|a| a.negated) {
        return None;
    }

    let one_idx = addends.iter().position(|a| is_one(a.expr))?;
    let or_idx = addends
        .iter()
        .enumerate()
        .find(|(idx, a)| *idx != one_idx && matches!(a.expr.kind, Kind::Or))
        .map(|(idx, _)| idx)?;
    let a_idx = (0..3).find(|idx| *idx != one_idx && *idx != or_idx)?;

    let a = addends[a_idx].expr;
    let or_node = addends[or_idx].expr;
    if or_node.children.len() != 2 {
        return None;
    }
    let lhs = &or_node.children[0];
    let rhs = &or_node.children[1];
    if is_not_of(lhs, a) {
        Some((a, rhs))
    } else if is_not_of(rhs, a) {
        Some((a, lhs))
    } else {
        None
    }
}

fn xor_via_or_not_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let mut addends = Vec::new();
    flatten_signed_addends(expr, false, &mut addends);
    if addends.len() != 4 {
        return None;
    }

    let neg_two_idx = addends
        .iter()
        .position(|a| a.negated && is_const_value(a.expr, 2))?;
    let two_or = addends.iter().enumerate().find_map(|(idx, a)| {
        if idx == neg_two_idx || !a.negated || !matches!(a.expr.kind, Kind::Mul) {
            return None;
        }
        let lhs = &a.expr.children[0];
        let rhs = &a.expr.children[1];
        if is_const_value(lhs, 2) && matches!(rhs.kind, Kind::Or) {
            Some((idx, rhs.as_ref()))
        } else if is_const_value(rhs, 2) && matches!(lhs.kind, Kind::Or) {
            Some((idx, lhs.as_ref()))
        } else {
            None
        }
    })?;

    let (mul_idx, or_node) = two_or;
    if or_node.children.len() != 2 {
        return None;
    }
    let remaining: Vec<_> = (0..4)
        .filter(|idx| *idx != neg_two_idx && *idx != mul_idx)
        .collect();
    if remaining.len() != 2 {
        return None;
    }
    let (a_idx, b_idx) = match (addends[remaining[0]].negated, addends[remaining[1]].negated) {
        (false, true) => (remaining[0], remaining[1]),
        (true, false) => (remaining[1], remaining[0]),
        _ => return None,
    };
    let a = addends[a_idx].expr;
    let b = addends[b_idx].expr;
    let lhs = &or_node.children[0];
    let rhs = &or_node.children[1];
    if (expr_eq(lhs, a) && is_not_of(rhs, b)) || (expr_eq(rhs, a) && is_not_of(lhs, b)) {
        Some((a, b))
    } else {
        None
    }
}

fn not_of_and_or(expr: &Expr) -> Option<(&Expr, &Expr, bool)> {
    if !matches!(expr.kind, Kind::And | Kind::Or) || expr.children.len() != 2 {
        return None;
    }
    Some((
        &expr.children[0],
        &expr.children[1],
        matches!(expr.kind, Kind::And),
    ))
}

fn is_xor_of(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::Xor)
        && expr.children.len() == 2
        && unordered_pair_eq(&expr.children[0], &expr.children[1], lhs, rhs)
}

fn is_add_of(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::Add)
        && expr.children.len() == 2
        && unordered_pair_eq(&expr.children[0], &expr.children[1], lhs, rhs)
}

fn is_scaled_add_of(expr: &Expr, lhs: &Expr, rhs: &Expr, coeff: u64) -> bool {
    if !matches!(expr.kind, Kind::Add) || expr.children.len() != 2 {
        return false;
    }
    let lhs_scaled = Expr::mul(Expr::constant(coeff), lhs.clone_tree());
    let rhs_scaled = Expr::mul(Expr::constant(coeff), rhs.clone_tree());
    unordered_pair_eq(
        &expr.children[0],
        &expr.children[1],
        &lhs_scaled,
        &rhs_scaled,
    )
}

fn is_and_of(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::And)
        && expr.children.len() == 2
        && unordered_pair_eq(&expr.children[0], &expr.children[1], lhs, rhs)
}

fn is_or_of(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::Or)
        && expr.children.len() == 2
        && unordered_pair_eq(&expr.children[0], &expr.children[1], lhs, rhs)
}

fn is_xor_lowering_of(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    let Kind::Add = expr.kind else {
        return false;
    };
    if expr.children.len() != 2 {
        return false;
    }
    let sum = &expr.children[0];
    let neg_two_and = &expr.children[1];
    if !matches!(sum.kind, Kind::Add)
        || sum.children.len() != 2
        || !unordered_pair_eq(&sum.children[0], &sum.children[1], lhs, rhs)
        || !matches!(neg_two_and.kind, Kind::Neg)
        || neg_two_and.children.len() != 1
    {
        return false;
    }
    let two_and = &neg_two_and.children[0];
    if !matches!(two_and.kind, Kind::Mul) || two_and.children.len() != 2 {
        return false;
    }
    let a = &two_and.children[0];
    let b = &two_and.children[1];
    (is_const_value(a, 2) && is_and_of(b, lhs, rhs))
        || (is_const_value(b, 2) && is_and_of(a, lhs, rhs))
}

fn is_or_of_not_pair(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::Or)
        && expr.children.len() == 2
        && ((is_not_of(&expr.children[0], lhs) && is_not_of(&expr.children[1], rhs))
            || (is_not_of(&expr.children[0], rhs) && is_not_of(&expr.children[1], lhs)))
}

fn is_and_of_not_pair(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::And)
        && expr.children.len() == 2
        && ((is_not_of(&expr.children[0], lhs) && is_not_of(&expr.children[1], rhs))
            || (is_not_of(&expr.children[0], rhs) && is_not_of(&expr.children[1], lhs)))
}

fn not_pair_operands<'a>(lhs: &'a Expr, rhs: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    if matches!(lhs.kind, Kind::Not)
        && lhs.children.len() == 1
        && matches!(rhs.kind, Kind::Not)
        && rhs.children.len() == 1
    {
        Some((&lhs.children[0], &rhs.children[0]))
    } else {
        None
    }
}

fn is_not_of_and(expr: &Expr, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(expr.kind, Kind::Not)
        && expr.children.len() == 1
        && is_and_of(&expr.children[0], lhs, rhs)
}

fn is_neg_add_all_ones_of(expr: &Expr, inner: &Expr) -> bool {
    if !matches!(expr.kind, Kind::Add) || expr.children.len() != 2 {
        return false;
    }
    let lhs = &expr.children[0];
    let rhs = &expr.children[1];
    (is_neg_of(lhs, inner) && is_all_ones(rhs)) || (is_neg_of(rhs, inner) && is_all_ones(lhs))
}

fn is_not_of(expr: &Expr, inner: &Expr) -> bool {
    matches!(expr.kind, Kind::Not) && expr.children.len() == 1 && expr_eq(&expr.children[0], inner)
}

fn is_neg_of(expr: &Expr, inner: &Expr) -> bool {
    matches!(expr.kind, Kind::Neg) && expr.children.len() == 1 && expr_eq(&expr.children[0], inner)
}

fn unordered_pair_eq(a: &Expr, b: &Expr, x: &Expr, y: &Expr) -> bool {
    (expr_eq(a, x) && expr_eq(b, y)) || (expr_eq(a, y) && expr_eq(b, x))
}

fn expr_eq(lhs: &Expr, rhs: &Expr) -> bool {
    lhs == rhs
}

fn is_zero(expr: &Expr) -> bool {
    matches!(expr.kind, Kind::Constant(0))
}

fn is_one(expr: &Expr) -> bool {
    matches!(expr.kind, Kind::Constant(1))
}

fn is_const_value(expr: &Expr, value: u64) -> bool {
    matches!(expr.kind, Kind::Constant(v) if v == value)
}

fn is_all_ones(expr: &Expr) -> bool {
    matches!(expr.kind, Kind::Constant(u64::MAX))
}

/// One theorem-backed local rewrite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertStep {
    pub theorem: LeanTheorem,
    pub path: ExprPath,
    pub context: ExprContext,
    pub before: Box<Expr>,
    pub after: Box<Expr>,
}

/// End-to-end certificate for `original == simplified` at `bitwidth`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanCertificate {
    pub bitwidth: u32,
    pub original: Box<Expr>,
    pub simplified: Box<Expr>,
    pub steps: Vec<CertStep>,
}

impl LeanCertificate {
    #[must_use]
    pub fn new(bitwidth: u32, original: Box<Expr>, simplified: Box<Expr>) -> Self {
        Self {
            bitwidth,
            original,
            simplified,
            steps: Vec::new(),
        }
    }

    pub fn push_step(
        &mut self,
        theorem: LeanTheorem,
        path: ExprPath,
        before: Box<Expr>,
        after: Box<Expr>,
    ) {
        self.steps.push(CertStep {
            theorem,
            path,
            context: ExprContext::default(),
            before,
            after,
        });
    }

    pub fn push_context_step(
        &mut self,
        theorem: LeanTheorem,
        context: ExprContext,
        before: Box<Expr>,
        after: Box<Expr>,
    ) {
        self.steps.push(CertStep {
            theorem,
            path: ExprPath::default(),
            context,
            before,
            after,
        });
    }

    #[must_use]
    pub fn try_single_rewrite_64(
        bitwidth: u32,
        original: Box<Expr>,
        path: ExprPath,
        after: Box<Expr>,
    ) -> Option<Self> {
        if bitwidth != 64 {
            return None;
        }
        let (context, before) = context_from_path(&original, &path)?;
        let theorem = identify_rewrite_theorem_64(&before, &after)?;
        let simplified = context.plug(after.clone_tree());
        let mut cert = Self::new(bitwidth, original, simplified);
        cert.steps.push(CertStep {
            theorem,
            path,
            context,
            before,
            after,
        });
        Some(cert)
    }

    #[must_use]
    pub fn try_single_rewrite_between_64(
        bitwidth: u32,
        original: Box<Expr>,
        simplified: Box<Expr>,
    ) -> Option<Self> {
        if bitwidth != 64 {
            return None;
        }

        fn go(
            bitwidth: u32,
            original_root: &Expr,
            simplified_root: &Expr,
            original_site: &Expr,
            simplified_site: &Expr,
            path: &mut Vec<u8>,
        ) -> Option<LeanCertificate> {
            if let Some(cert) = LeanCertificate::try_single_rewrite_64(
                bitwidth,
                original_root.clone_tree(),
                ExprPath(path.clone()),
                simplified_site.clone_tree(),
            ) {
                if *cert.simplified == *simplified_root {
                    return Some(cert);
                }
            }

            if original_site.kind != simplified_site.kind
                || original_site.children.len() != simplified_site.children.len()
                || original_site.children.len() > usize::from(u8::MAX)
            {
                return None;
            }

            for (idx, (before_child, after_child)) in original_site
                .children
                .iter()
                .zip(simplified_site.children.iter())
                .enumerate()
            {
                path.push(u8::try_from(idx).ok()?);
                if let Some(cert) = go(
                    bitwidth,
                    original_root,
                    simplified_root,
                    before_child,
                    after_child,
                    path,
                ) {
                    path.pop();
                    return Some(cert);
                }
                path.pop();
            }
            None
        }

        go(
            bitwidth,
            &original,
            &simplified,
            &original,
            &simplified,
            &mut Vec::new(),
        )
    }

    #[must_use]
    pub fn merge_step_chain(mut self, next: Self) -> Option<Self> {
        if self.bitwidth != next.bitwidth || *self.simplified != *next.original {
            return None;
        }
        self.simplified = next.simplified;
        self.steps.extend(next.steps);
        Some(self)
    }

    #[must_use]
    pub fn matches_endpoints(&self, bitwidth: u32, original: &Expr, simplified: &Expr) -> bool {
        self.bitwidth == bitwidth && *self.original == *original && *self.simplified == *simplified
    }
}

/// Finite truth-table certificate for a candidate expression in a reduced
/// signature subproblem. This is intentionally separate from
/// [`LeanCertificate`]: it proves `SignatureSpec`, not full original-expression
/// semantic equivalence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSignatureCertificate {
    pub bitwidth: u32,
    pub num_vars: u32,
    pub signature: Vec<u64>,
    pub expr: Box<Expr>,
}

impl LeanSignatureCertificate {
    #[must_use]
    pub fn new(bitwidth: u32, num_vars: u32, signature: Vec<u64>, expr: Box<Expr>) -> Option<Self> {
        let expected_len = 1usize.checked_shl(num_vars)?;
        if signature.len() != expected_len {
            return None;
        }
        Some(Self {
            bitwidth,
            num_vars,
            signature,
            expr,
        })
    }

    #[must_use]
    pub fn matches_signature(
        &self,
        bitwidth: u32,
        num_vars: u32,
        signature: &[u64],
        expr: &Expr,
    ) -> bool {
        self.bitwidth == bitwidth
            && self.num_vars == num_vars
            && self.signature == signature
            && *self.expr == *expr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theorem_names_match_lean_exports() {
        assert_eq!(
            LeanTheorem::XorEqAddSubTwoMulAnd64.lean_name(),
            "Cobra.xor_eq_add_sub_two_mul_and_64"
        );
        assert_eq!(
            LeanTheorem::CompileSound.lean_name(),
            "Cobra.Expr.compile_sound"
        );
        assert_eq!(
            LeanTheorem::ContextPreservesSemanticEquivalence.lean_name(),
            "Cobra.Ctx.plug_preserves_sem_eq"
        );
        assert_eq!(LeanTheorem::ShrZero64.lean_name(), "Cobra.shr_zero_64");
        assert_eq!(
            LeanTheorem::AndAllOnes64.lean_name(),
            "Cobra.and_all_ones_64"
        );
        assert_eq!(
            LeanTheorem::DemorganNotOr64.lean_name(),
            "Cobra.demorgan_not_or_64"
        );
        assert_eq!(
            LeanTheorem::DemorganOrNotNot64.lean_name(),
            "Cobra.demorgan_or_not_not_64"
        );
        assert_eq!(
            LeanTheorem::DemorganNotAndNotNot64.lean_name(),
            "Cobra.demorgan_not_and_not_not_64"
        );
        assert_eq!(
            LeanTheorem::DemorganNotOrNotNot64.lean_name(),
            "Cobra.demorgan_not_or_not_not_64"
        );
        assert_eq!(
            LeanTheorem::BnotEqNegAddAllOnes64.lean_name(),
            "Cobra.bnot_eq_neg_add_all_ones_64"
        );
    }

    #[test]
    fn certificate_collects_steps() {
        let original = Expr::xor(Expr::variable(0), Expr::variable(1));
        let simplified = Expr::add(Expr::variable(0), Expr::variable(1));
        let mut cert = LeanCertificate::new(64, original.clone_tree(), simplified.clone_tree());
        cert.push_step(
            LeanTheorem::XorEqAddSubTwoMulAnd64,
            ExprPath::default(),
            original,
            simplified,
        );
        assert_eq!(cert.bitwidth, 64);
        assert_eq!(cert.steps.len(), 1);
        assert_eq!(
            cert.steps[0].theorem.lean_name(),
            "Cobra.xor_eq_add_sub_two_mul_and_64"
        );
    }

    #[test]
    fn certificate_collects_context_steps() {
        let before = Expr::xor(Expr::variable(0), Expr::constant(0));
        let after = Expr::variable(0);
        let mut cert = LeanCertificate::new(64, before.clone_tree(), after.clone_tree());
        cert.push_context_step(
            LeanTheorem::XorZero64,
            ExprContext {
                frames: vec![ContextFrame::AddL {
                    rhs: Expr::constant(1),
                }],
            },
            before,
            after,
        );
        assert_eq!(cert.steps.len(), 1);
        assert_eq!(cert.steps[0].context.frames.len(), 1);
    }

    #[test]
    fn context_from_path_rebuilds_root() {
        let root = Expr::add(
            Expr::variable(0),
            Expr::and(Expr::variable(1), Expr::constant(0)),
        );
        let (context, target) =
            context_from_path(&root, &ExprPath(vec![1, 0])).expect("valid path");
        assert_eq!(*target, *Expr::variable(1));
        assert_eq!(*context.plug(target), *root);
    }

    #[test]
    fn context_from_path_rejects_invalid_child() {
        let root = Expr::not(Expr::variable(0));
        assert!(context_from_path(&root, &ExprPath(vec![1])).is_none());
    }

    #[test]
    fn identifies_atom_simplifier_rules() {
        let x = Expr::variable(0);
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::and(x.clone_tree(), Expr::constant(0)),
                &Expr::constant(0)
            ),
            Some(LeanTheorem::AndZero64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(&Expr::or(Expr::constant(0), x.clone_tree()), &x),
            Some(LeanTheorem::ZeroOr64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(&Expr::not(Expr::not(x.clone_tree())), &x),
            Some(LeanTheorem::NotNot64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(&Expr::shr(x.clone_tree(), 0), &x),
            Some(LeanTheorem::ShrZero64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::and(Expr::constant(3), Expr::constant(1)),
                &Expr::constant(1)
            ),
            Some(LeanTheorem::Const3And1_64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::and(Expr::constant(1), Expr::constant(3)),
                &Expr::constant(1)
            ),
            None
        );
        let y = Expr::variable(1);
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::or(Expr::not(x.clone_tree()), Expr::not(y.clone_tree())),
                &Expr::not(Expr::and(x.clone_tree(), y.clone_tree()))
            ),
            Some(LeanTheorem::DemorganOrNotNot64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::not(Expr::and(
                    Expr::not(x.clone_tree()),
                    Expr::not(y.clone_tree())
                )),
                &Expr::or(x.clone_tree(), y.clone_tree())
            ),
            Some(LeanTheorem::DemorganNotAndNotNot64)
        );
        assert_eq!(
            identify_rewrite_theorem_64(
                &Expr::not(Expr::or(
                    Expr::not(x.clone_tree()),
                    Expr::not(y.clone_tree())
                )),
                &Expr::and(x.clone_tree(), y.clone_tree())
            ),
            Some(LeanTheorem::DemorganNotOrNotNot64)
        );
    }

    #[test]
    fn identifies_or_minus_and_identity() {
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let before = Expr::add(
            Expr::or(x.clone_tree(), y.clone_tree()),
            Expr::neg(Expr::and(x.clone_tree(), y.clone_tree())),
        );
        let after = Expr::xor(x, y);
        assert_eq!(
            identify_rewrite_theorem_64(&before, &after),
            Some(LeanTheorem::OrSubAndEqXor64)
        );
    }

    #[test]
    fn identifies_and_or_sum_identity() {
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let before = Expr::add(
            Expr::and(x.clone_tree(), y.clone_tree()),
            Expr::or(x.clone_tree(), y.clone_tree()),
        );
        let after = Expr::add(x, y);
        assert_eq!(
            identify_rewrite_theorem_64(&before, &after),
            Some(LeanTheorem::AndOrSumEqAdd64)
        );
    }

    #[test]
    fn identifies_xor_lowering_identity() {
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let before = Expr::xor(x.clone_tree(), y.clone_tree());
        let after = Expr::add(
            Expr::add(x.clone_tree(), y.clone_tree()),
            Expr::neg(Expr::mul(
                Expr::constant(2),
                Expr::and(x.clone_tree(), y.clone_tree()),
            )),
        );
        assert_eq!(
            identify_rewrite_theorem_64(&before, &after),
            Some(LeanTheorem::XorEqAddSubTwoMulAnd64)
        );
    }

    #[test]
    fn identifies_not_over_arith_lowering() {
        let x = Expr::add(Expr::variable(0), Expr::constant(1));
        let before = Expr::not(x.clone_tree());
        let after = Expr::add(Expr::neg(x), Expr::constant(u64::MAX));
        assert_eq!(
            identify_rewrite_theorem_64(&before, &after),
            Some(LeanTheorem::BnotEqNegAddAllOnes64)
        );
    }

    #[test]
    fn single_rewrite_certificate_uses_path_context() {
        let x = Expr::variable(0);
        let root = Expr::add(
            Expr::variable(1),
            Expr::and(x.clone_tree(), Expr::constant(0)),
        );
        let cert = LeanCertificate::try_single_rewrite_64(
            64,
            root.clone_tree(),
            ExprPath(vec![1]),
            Expr::constant(0),
        )
        .expect("certificate");
        assert_eq!(*cert.original, *root);
        assert_eq!(
            *cert.simplified,
            *Expr::add(Expr::variable(1), Expr::constant(0))
        );
        assert_eq!(cert.steps[0].theorem, LeanTheorem::AndZero64);
    }

    #[test]
    fn single_rewrite_between_finds_nested_site() {
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let z = Expr::variable(2);
        let original = Expr::add(
            Expr::add(
                Expr::or(x.clone_tree(), y.clone_tree()),
                Expr::neg(Expr::and(x.clone_tree(), y.clone_tree())),
            ),
            z.clone_tree(),
        );
        let simplified = Expr::add(Expr::xor(x, y), z);
        let cert = LeanCertificate::try_single_rewrite_between_64(
            64,
            original.clone_tree(),
            simplified.clone_tree(),
        )
        .expect("nested rewrite certificate");
        assert!(cert.matches_endpoints(64, &original, &simplified));
        assert_eq!(cert.steps[0].path, ExprPath(vec![0]));
        assert_eq!(cert.steps[0].theorem, LeanTheorem::OrSubAndEqXor64);
    }

    #[test]
    fn merge_step_chain_requires_continuity() {
        let first = LeanCertificate::new(
            64,
            Expr::variable(0),
            Expr::add(Expr::variable(0), Expr::constant(0)),
        );
        let second = LeanCertificate::new(
            64,
            Expr::add(Expr::variable(0), Expr::constant(0)),
            Expr::variable(0),
        );
        assert!(first.merge_step_chain(second).is_some());
    }

    #[test]
    fn endpoint_match_checks_width_original_and_simplified() {
        let original = Expr::add(Expr::variable(0), Expr::constant(0));
        let simplified = Expr::variable(0);
        let cert = LeanCertificate::new(64, original.clone_tree(), simplified.clone_tree());
        assert!(cert.matches_endpoints(64, &original, &simplified));
        assert!(!cert.matches_endpoints(32, &original, &simplified));
        assert!(!cert.matches_endpoints(64, &simplified, &simplified));
        assert!(!cert.matches_endpoints(64, &original, &original));
    }

    #[test]
    fn signature_certificate_checks_table_width_and_expr() {
        let expr = Expr::xor(Expr::variable(0), Expr::variable(1));
        let cert =
            LeanSignatureCertificate::new(64, 2, vec![0, 1, 1, 0], expr.clone_tree()).unwrap();
        assert!(cert.matches_signature(64, 2, &[0, 1, 1, 0], &expr));
        assert!(!cert.matches_signature(32, 2, &[0, 1, 1, 0], &expr));
        assert!(!cert.matches_signature(64, 1, &[0, 1], &expr));
        assert!(!cert.matches_signature(64, 2, &[0, 0, 0, 1], &expr));
        assert!(!cert.matches_signature(64, 2, &[0, 1, 1, 0], &Expr::variable(0)));
        assert!(LeanSignatureCertificate::new(64, 2, vec![0, 1], expr).is_none());
    }
}
