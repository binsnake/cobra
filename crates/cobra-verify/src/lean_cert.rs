//! Lean certificate data model.
//!
//! This module intentionally contains only stable, serializable-by-caller
//! data shapes. It does not invoke Lean; callers can emit these certificates
//! alongside candidate expressions and an external checker can replay them
//! against the theorem pack in `formal/lean`.

use crate::core::expr::Expr;
use crate::core::expr::Kind;
use crate::core::width::{is_uniform_width, validate_widths};
use std::sync::Arc;

use crate::verify::lean_match::{
    add_with_neg_operands, and_or_sum_operands, expr_eq, is_all_ones_at, is_and_not_of,
    is_const_value, is_not_of, is_one, is_zero, not_or_add_self_add_one_operands,
    not_or_minus_not_operands, same_or_and_operands, scaled_and_or_sum_operands, unordered_pair_eq,
    xor_and_absorb_operands, xor_via_or_not_operands,
};

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
    XorAddTwoMulAndEqAdd64,
    OrSubAndEqXor64,
    AndOrSumEqAdd64,
    TwoMulAndOrSumEqTwoMulAdd64,
    NotOrSubNotEqAnd64,
    NotOrAddSelfAddOneEqAnd64,
    XorViaOrNot64,
    XorAndEqAndNot64,
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
    AndNotSelf64,
    NotAndSelf64,
    OrNotSelf64,
    NotOrSelf64,
    XorNotSelf64,
    NotXorSelf64,
    AndOrAbsorb64,
    AndOrAbsorbRight64,
    OrAndAbsorb64,
    OrAndAbsorbRight64,
    AndOrAbsorbComm64,
    AndOrAbsorbCommRight64,
    OrAndAbsorbComm64,
    OrAndAbsorbCommRight64,
    AndConstAssoc64,
    OrConstAssoc64,
    XorConstAssoc64,
    ZextIdentityW,
    TruncIdentityW,
    SextIdentityW,
    ZextZextW,
    TruncTruncW,
    TruncZextW,
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
        Self::XorAddTwoMulAndEqAdd64,
        Self::OrSubAndEqXor64,
        Self::AndOrSumEqAdd64,
        Self::TwoMulAndOrSumEqTwoMulAdd64,
        Self::NotOrSubNotEqAnd64,
        Self::NotOrAddSelfAddOneEqAnd64,
        Self::XorViaOrNot64,
        Self::XorAndEqAndNot64,
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
        Self::AndNotSelf64,
        Self::NotAndSelf64,
        Self::OrNotSelf64,
        Self::NotOrSelf64,
        Self::XorNotSelf64,
        Self::NotXorSelf64,
        Self::AndConstAssoc64,
        Self::OrConstAssoc64,
        Self::XorConstAssoc64,
        Self::ZextIdentityW,
        Self::TruncIdentityW,
        Self::SextIdentityW,
        Self::ZextZextW,
        Self::TruncTruncW,
        Self::TruncZextW,
        Self::AndOrAbsorb64,
        Self::AndOrAbsorbRight64,
        Self::OrAndAbsorb64,
        Self::OrAndAbsorbRight64,
        Self::AndOrAbsorbComm64,
        Self::AndOrAbsorbCommRight64,
        Self::OrAndAbsorbComm64,
        Self::OrAndAbsorbCommRight64,
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
        Self::XorAddTwoMulAndEqAdd64,
        Self::OrSubAndEqXor64,
        Self::AndOrSumEqAdd64,
        Self::TwoMulAndOrSumEqTwoMulAdd64,
        Self::NotOrAddSelfAddOneEqAnd64,
        Self::XorViaOrNot64,
        Self::XorAndEqAndNot64,
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
        Self::AndNotSelf64,
        Self::NotAndSelf64,
        Self::OrNotSelf64,
        Self::NotOrSelf64,
        Self::XorNotSelf64,
        Self::NotXorSelf64,
        Self::AndOrAbsorb64,
        Self::AndOrAbsorbRight64,
        Self::OrAndAbsorb64,
        Self::OrAndAbsorbRight64,
        Self::AndOrAbsorbComm64,
        Self::AndOrAbsorbCommRight64,
        Self::OrAndAbsorbComm64,
        Self::OrAndAbsorbCommRight64,
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

    /// Mixed-width (`MExpr`-world) rewrites recognized by
    /// [`identify_mixed_rewrite_theorem_at`]. Kept separate from
    /// [`Self::RECOGNIZED_REWRITE_64`]: these are citable only through the
    /// mixed certificate path, and are width-generic by construction, so they
    /// hold at every valid bitwidth.
    pub const RECOGNIZED_MIXED_REWRITE: &'static [Self] = &[
        Self::ZextIdentityW,
        Self::TruncIdentityW,
        Self::SextIdentityW,
        Self::ZextZextW,
        Self::TruncTruncW,
        Self::TruncZextW,
    ];

    /// Name of this theorem's width-generic counterpart in the Lean pack, if
    /// it has one.
    ///
    /// The `_64` pack is stated over `BitVec 64`, so a certificate citing it is
    /// replayable only at that width -- which made every width in 1..=63
    /// unsimplifiable once the public gate began requiring a certificate. The
    /// pure bitwise and ring identities hold at every width and have `_w`
    /// counterparts; the arithmetic MBA identities do not, because their proofs
    /// need carry reasoning `bv_decide` cannot discharge without a concrete
    /// width.
    #[must_use]
    pub const fn width_parametric_lean_name(self) -> Option<&'static str> {
        match self {
            Self::AddZero64 => Some("Cobra.add_zero_w"),
            Self::ZeroAdd64 => Some("Cobra.zero_add_w"),
            Self::MulZero64 => Some("Cobra.mul_zero_w"),
            Self::ZeroMul64 => Some("Cobra.zero_mul_w"),
            Self::MulOne64 => Some("Cobra.mul_one_w"),
            Self::OneMul64 => Some("Cobra.one_mul_w"),
            Self::NegNeg64 => Some("Cobra.neg_neg_w"),
            Self::NotNot64 => Some("Cobra.not_not_w"),
            Self::AndSelf64 => Some("Cobra.and_self_w"),
            Self::OrSelf64 => Some("Cobra.or_self_w"),
            Self::XorSelf64 => Some("Cobra.xor_self_w"),
            Self::XorZero64 => Some("Cobra.xor_zero_w"),
            Self::ZeroXor64 => Some("Cobra.zero_xor_w"),
            Self::AndZero64 => Some("Cobra.and_zero_w"),
            Self::ZeroAnd64 => Some("Cobra.zero_and_w"),
            Self::OrZero64 => Some("Cobra.or_zero_w"),
            Self::ZeroOr64 => Some("Cobra.zero_or_w"),
            Self::ShrZero64 => Some("Cobra.shr_zero_w"),
            Self::AndAllOnes64 => Some("Cobra.and_all_ones_w"),
            Self::AllOnesAnd64 => Some("Cobra.all_ones_and_w"),
            Self::OrAllOnes64 => Some("Cobra.or_all_ones_w"),
            Self::AllOnesOr64 => Some("Cobra.all_ones_or_w"),
            Self::AndNotSelf64 => Some("Cobra.and_not_self_w"),
            Self::NotAndSelf64 => Some("Cobra.not_and_self_w"),
            Self::OrNotSelf64 => Some("Cobra.or_not_self_w"),
            Self::NotOrSelf64 => Some("Cobra.not_or_self_w"),
            Self::XorNotSelf64 => Some("Cobra.xor_not_self_w"),
            Self::NotXorSelf64 => Some("Cobra.not_xor_self_w"),
            Self::AndOrAbsorb64 => Some("Cobra.and_or_absorb_w"),
            Self::AndOrAbsorbRight64 => Some("Cobra.and_or_absorb_right_w"),
            Self::OrAndAbsorb64 => Some("Cobra.or_and_absorb_w"),
            Self::OrAndAbsorbRight64 => Some("Cobra.or_and_absorb_right_w"),
            Self::AndOrAbsorbComm64 => Some("Cobra.and_or_absorb_comm_w"),
            Self::AndOrAbsorbCommRight64 => Some("Cobra.and_or_absorb_comm_right_w"),
            Self::OrAndAbsorbComm64 => Some("Cobra.or_and_absorb_comm_w"),
            Self::OrAndAbsorbCommRight64 => Some("Cobra.or_and_absorb_comm_right_w"),
            Self::DemorganNotAnd64 => Some("Cobra.demorgan_not_and_w"),
            Self::DemorganOrNotNot64 => Some("Cobra.demorgan_or_not_not_w"),
            Self::DemorganNotOr64 => Some("Cobra.demorgan_not_or_w"),
            Self::DemorganNotAndNotNot64 => Some("Cobra.demorgan_and_not_not_w"),
            _ => None,
        }
    }

    /// `true` when this theorem can be cited at any bitwidth.
    #[must_use]
    pub const fn is_width_parametric(self) -> bool {
        self.width_parametric_lean_name().is_some()
    }

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
            Self::XorAddTwoMulAndEqAdd64 => "Cobra.xor_add_two_mul_and_eq_add_64",
            Self::OrSubAndEqXor64 => "Cobra.or_sub_and_eq_xor_64",
            Self::AndOrSumEqAdd64 => "Cobra.and_or_sum_eq_add_64",
            Self::TwoMulAndOrSumEqTwoMulAdd64 => "Cobra.two_mul_and_or_sum_eq_two_mul_add_64",
            Self::NotOrSubNotEqAnd64 => "Cobra.not_or_sub_not_eq_and_64",
            Self::NotOrAddSelfAddOneEqAnd64 => "Cobra.not_or_add_self_add_one_eq_and_64",
            Self::XorViaOrNot64 => "Cobra.xor_via_or_not_64",
            Self::XorAndEqAndNot64 => "Cobra.xor_and_eq_and_not_64",
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
            Self::AndNotSelf64 => "Cobra.and_not_self_64",
            Self::NotAndSelf64 => "Cobra.not_and_self_64",
            Self::OrNotSelf64 => "Cobra.or_not_self_64",
            Self::NotOrSelf64 => "Cobra.not_or_self_64",
            Self::XorNotSelf64 => "Cobra.xor_not_self_64",
            Self::NotXorSelf64 => "Cobra.not_xor_self_64",
            Self::AndOrAbsorb64 => "Cobra.and_or_absorb_64",
            Self::AndOrAbsorbRight64 => "Cobra.and_or_absorb_right_64",
            Self::OrAndAbsorb64 => "Cobra.or_and_absorb_64",
            Self::OrAndAbsorbRight64 => "Cobra.or_and_absorb_right_64",
            Self::AndOrAbsorbComm64 => "Cobra.and_or_absorb_comm_64",
            Self::AndOrAbsorbCommRight64 => "Cobra.and_or_absorb_comm_right_64",
            Self::OrAndAbsorbComm64 => "Cobra.or_and_absorb_comm_64",
            Self::OrAndAbsorbCommRight64 => "Cobra.or_and_absorb_comm_right_64",
            Self::AndConstAssoc64 => "Cobra.and_const_assoc_64",
            Self::OrConstAssoc64 => "Cobra.or_const_assoc_64",
            Self::XorConstAssoc64 => "Cobra.xor_const_assoc_64",
            Self::ZextIdentityW => "Cobra.MExpr.zext_identity",
            Self::TruncIdentityW => "Cobra.MExpr.trunc_identity",
            Self::SextIdentityW => "Cobra.MExpr.sext_identity",
            Self::ZextZextW => "Cobra.MExpr.zext_zext",
            Self::TruncTruncW => "Cobra.MExpr.trunc_trunc",
            Self::TruncZextW => "Cobra.MExpr.trunc_zext",
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
    AddL { rhs: Arc<Expr> },
    AddR { lhs: Arc<Expr> },
    MulL { rhs: Arc<Expr> },
    MulR { lhs: Arc<Expr> },
    AndL { rhs: Arc<Expr> },
    AndR { lhs: Arc<Expr> },
    OrL { rhs: Arc<Expr> },
    OrR { lhs: Arc<Expr> },
    XorL { rhs: Arc<Expr> },
    XorR { lhs: Arc<Expr> },
    Not,
    Neg,
    Shr { amount: u32 },
    ZExt { w: u32 },
    SExt { w: u32 },
    Trunc { w: u32 },
    ConcatHi { lo: Arc<Expr> },
    ConcatLo { hi: Arc<Expr> },
}

/// Explicit context payload corresponding to `Cobra.Ctx`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExprContext {
    pub frames: Vec<ContextFrame>,
}

impl ExprContext {
    #[must_use]
    pub fn plug(&self, mut expr: Arc<Expr>) -> Arc<Expr> {
        for frame in &self.frames {
            expr = frame.plug(expr);
        }
        expr
    }
}

impl ContextFrame {
    #[must_use]
    pub fn plug(&self, expr: Arc<Expr>) -> Arc<Expr> {
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
            Self::ZExt { w } => Expr::zext(expr, *w),
            Self::SExt { w } => Expr::sext(expr, *w),
            Self::Trunc { w } => Expr::trunc(expr, *w),
            Self::ConcatHi { lo } => Expr::concat(expr, lo.clone_tree()),
            Self::ConcatLo { hi } => Expr::concat(hi.clone_tree(), expr),
        }
    }
}

#[must_use]
pub fn context_from_path(root: &Expr, path: &ExprPath) -> Option<(ExprContext, Arc<Expr>)> {
    let mut current = root;
    let mut root_to_site = Vec::new();

    for &child_index in &path.0 {
        let index = usize::from(child_index);
        let frame = match &current.kind {
            crate::core::expr::Kind::Add if current.children.len() == 2 => match index {
                0 => ContextFrame::AddL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::AddR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            crate::core::expr::Kind::Mul if current.children.len() == 2 => match index {
                0 => ContextFrame::MulL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::MulR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            crate::core::expr::Kind::And if current.children.len() == 2 => match index {
                0 => ContextFrame::AndL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::AndR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            crate::core::expr::Kind::Or if current.children.len() == 2 => match index {
                0 => ContextFrame::OrL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::OrR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            crate::core::expr::Kind::Xor if current.children.len() == 2 => match index {
                0 => ContextFrame::XorL {
                    rhs: current.children[1].clone_tree(),
                },
                1 => ContextFrame::XorR {
                    lhs: current.children[0].clone_tree(),
                },
                _ => return None,
            },
            crate::core::expr::Kind::Not if current.children.len() == 1 && index == 0 => {
                ContextFrame::Not
            }
            crate::core::expr::Kind::Neg if current.children.len() == 1 && index == 0 => {
                ContextFrame::Neg
            }
            crate::core::expr::Kind::Shr(amount) if current.children.len() == 1 && index == 0 => {
                ContextFrame::Shr { amount: *amount }
            }
            crate::core::expr::Kind::ZExt(w) if current.children.len() == 1 && index == 0 => {
                ContextFrame::ZExt { w: *w }
            }
            crate::core::expr::Kind::SExt(w) if current.children.len() == 1 && index == 0 => {
                ContextFrame::SExt { w: *w }
            }
            crate::core::expr::Kind::Trunc(w) if current.children.len() == 1 && index == 0 => {
                ContextFrame::Trunc { w: *w }
            }
            crate::core::expr::Kind::Concat if current.children.len() == 2 => match index {
                0 => ContextFrame::ConcatHi {
                    lo: current.children[1].clone_tree(),
                },
                1 => ContextFrame::ConcatLo {
                    hi: current.children[0].clone_tree(),
                },
                _ => return None,
            },
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
#[allow(clippy::too_many_lines)]
pub fn identify_rewrite_theorem_64(before: &Expr, after: &Expr) -> Option<LeanTheorem> {
    identify_rewrite_theorem_at(64, before, after)
}

/// Width-aware form of [`identify_rewrite_theorem_64`]. Only the all-ones
/// constant depends on the width; every other shape is width-agnostic.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn identify_rewrite_theorem_at(
    bitwidth: u32,
    before: &Expr,
    after: &Expr,
) -> Option<LeanTheorem> {
    use LeanTheorem as Thm;

    match &before.kind {
        Kind::Add if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if let Some((a, b)) = xor_add_two_mul_and_operands(before) {
                if is_add_of(after, a, b) {
                    return Some(Thm::XorAddTwoMulAndEqAdd64);
                }
            }
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
            // Complement: x & ~x -> 0, both operand orders.
            if is_not_of(rhs, lhs) && is_zero(after) {
                return Some(Thm::AndNotSelf64);
            }
            if is_not_of(lhs, rhs) && is_zero(after) {
                return Some(Thm::NotAndSelf64);
            }
            // Absorption: x & (x | y) -> x, in all four operand orders.
            if expr_eq(lhs, after) && rhs.kind == Kind::Or && rhs.children.len() == 2 {
                if expr_eq(&rhs.children[0], lhs) {
                    return Some(Thm::AndOrAbsorb64);
                }
                if expr_eq(&rhs.children[1], lhs) {
                    return Some(Thm::AndOrAbsorbRight64);
                }
            }
            if expr_eq(rhs, after) && lhs.kind == Kind::Or && lhs.children.len() == 2 {
                if expr_eq(&lhs.children[0], rhs) {
                    return Some(Thm::AndOrAbsorbComm64);
                }
                if expr_eq(&lhs.children[1], rhs) {
                    return Some(Thm::AndOrAbsorbCommRight64);
                }
            }
            if is_zero(lhs) && is_zero(after) {
                return Some(Thm::ZeroAnd64);
            }
            if is_all_ones_at(rhs, bitwidth) && expr_eq(lhs, after) {
                return Some(Thm::AndAllOnes64);
            }
            if is_all_ones_at(lhs, bitwidth) && expr_eq(rhs, after) {
                return Some(Thm::AllOnesAnd64);
            }
        }
        Kind::Or if before.children.len() == 2 => {
            let lhs = &before.children[0];
            let rhs = &before.children[1];
            if expr_eq(lhs, rhs) && expr_eq(lhs, after) {
                return Some(Thm::OrSelf64);
            }
            if is_not_of(rhs, lhs) && is_all_ones_at(after, bitwidth) {
                return Some(Thm::OrNotSelf64);
            }
            if is_not_of(lhs, rhs) && is_all_ones_at(after, bitwidth) {
                return Some(Thm::NotOrSelf64);
            }
            if expr_eq(lhs, after) && rhs.kind == Kind::And && rhs.children.len() == 2 {
                if expr_eq(&rhs.children[0], lhs) {
                    return Some(Thm::OrAndAbsorb64);
                }
                if expr_eq(&rhs.children[1], lhs) {
                    return Some(Thm::OrAndAbsorbRight64);
                }
            }
            if expr_eq(rhs, after) && lhs.kind == Kind::And && lhs.children.len() == 2 {
                if expr_eq(&lhs.children[0], rhs) {
                    return Some(Thm::OrAndAbsorbComm64);
                }
                if expr_eq(&lhs.children[1], rhs) {
                    return Some(Thm::OrAndAbsorbCommRight64);
                }
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
            if is_all_ones_at(rhs, bitwidth) && is_all_ones_at(after, bitwidth) {
                return Some(Thm::OrAllOnes64);
            }
            if is_all_ones_at(lhs, bitwidth) && is_all_ones_at(after, bitwidth) {
                return Some(Thm::AllOnesOr64);
            }
        }
        Kind::Xor if before.children.len() == 2 => {
            {
                let lhs = &before.children[0];
                let rhs = &before.children[1];
                if is_not_of(rhs, lhs) && is_all_ones_at(after, bitwidth) {
                    return Some(Thm::XorNotSelf64);
                }
                if is_not_of(lhs, rhs) && is_all_ones_at(after, bitwidth) {
                    return Some(Thm::NotXorSelf64);
                }
            }
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
            if let Some((x, y)) = xor_and_absorb_operands(before) {
                if is_and_not_of(after, x, y) {
                    return Some(Thm::XorAndEqAndNot64);
                }
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
            if is_neg_add_all_ones_of(after, child, bitwidth) {
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

/// Recognize one mixed-width rewrite step.
///
/// A step is either a cast rewrite from the `MExpr` theorem pack, or a
/// uniform rewrite on a cast-free redex. A cast-free redex is always at the
/// global width: only cast nodes change width, and a cast-free subtree's
/// leaves are variables and constants, which default to `bitwidth`.
///
/// Every recognized step preserves the redex width, which
/// `MCtx.plug_preserves_sem_eq_w` requires — the surrounding context masks at
/// the width of its (plugged) child, so a width-changing rewrite would change
/// every enclosing mask.
#[must_use]
pub fn identify_mixed_rewrite_theorem_at(
    bitwidth: u32,
    before: &Expr,
    after: &Expr,
) -> Option<LeanTheorem> {
    use crate::core::width::width_of;
    use LeanTheorem as Thm;

    let w_before = width_of(before, &[], bitwidth);
    if w_before == 0 || w_before != width_of(after, &[], bitwidth) {
        return None;
    }

    if is_uniform_width(before, &[], bitwidth) && is_uniform_width(after, &[], bitwidth) {
        let theorem = identify_rewrite_theorem_at(bitwidth, before, after)?;
        // The same rule as the uniform path: off 64, only a theorem with a
        // width-generic counterpart is citable.
        if bitwidth != 64 && !theorem.is_width_parametric() {
            return None;
        }
        return Some(theorem);
    }

    match &before.kind {
        Kind::ZExt(w) if before.children.len() == 1 => {
            let inner = &before.children[0];
            if expr_eq(inner, after) && width_of(inner, &[], bitwidth) == *w {
                return Some(Thm::ZextIdentityW);
            }
            if let Kind::ZExt(w1) = &inner.kind {
                let base = &inner.children[0];
                if let Kind::ZExt(w2) = &after.kind {
                    if w2 == w
                        && expr_eq(&after.children[0], base)
                        && width_of(base, &[], bitwidth) <= *w1
                    {
                        return Some(Thm::ZextZextW);
                    }
                }
            }
        }
        Kind::SExt(w) if before.children.len() == 1 => {
            let inner = &before.children[0];
            if expr_eq(inner, after) && width_of(inner, &[], bitwidth) == *w {
                return Some(Thm::SextIdentityW);
            }
        }
        Kind::Trunc(w) if before.children.len() == 1 => {
            let inner = &before.children[0];
            if expr_eq(inner, after) && width_of(inner, &[], bitwidth) == *w {
                return Some(Thm::TruncIdentityW);
            }
            match &inner.kind {
                Kind::Trunc(w1) => {
                    let base = &inner.children[0];
                    if let Kind::Trunc(w2) = &after.kind {
                        if w2 == w && expr_eq(&after.children[0], base) && *w <= *w1 {
                            return Some(Thm::TruncTruncW);
                        }
                    }
                }
                Kind::ZExt(w1) => {
                    let base = &inner.children[0];
                    let base_w = width_of(base, &[], bitwidth);
                    if expr_eq(base, after) && base_w <= *w1 && base_w == *w {
                        return Some(Thm::TruncZextW);
                    }
                }
                _ => {}
            }
        }
        _ => {}
    }
    None
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

fn xor_add_two_mul_and_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if !matches!(expr.kind, Kind::Add) || expr.children.len() != 2 {
        return None;
    }
    for (xor, scaled_and) in [
        (&expr.children[0], &expr.children[1]),
        (&expr.children[1], &expr.children[0]),
    ] {
        if !matches!(xor.kind, Kind::Xor)
            || xor.children.len() != 2
            || !matches!(scaled_and.kind, Kind::Mul)
            || scaled_and.children.len() != 2
        {
            continue;
        }
        let and = if is_const_value(&scaled_and.children[0], 2) {
            &scaled_and.children[1]
        } else if is_const_value(&scaled_and.children[1], 2) {
            &scaled_and.children[0]
        } else {
            continue;
        };
        if matches!(and.kind, Kind::And)
            && and.children.len() == 2
            && unordered_pair_eq(
                &xor.children[0],
                &xor.children[1],
                &and.children[0],
                &and.children[1],
            )
        {
            return Some((&xor.children[0], &xor.children[1]));
        }
    }
    None
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

fn is_neg_add_all_ones_of(expr: &Expr, inner: &Expr, bitwidth: u32) -> bool {
    if !matches!(expr.kind, Kind::Add) || expr.children.len() != 2 {
        return false;
    }
    let lhs = &expr.children[0];
    let rhs = &expr.children[1];
    (is_neg_of(lhs, inner) && is_all_ones_at(rhs, bitwidth))
        || (is_neg_of(rhs, inner) && is_all_ones_at(lhs, bitwidth))
}

fn is_neg_of(expr: &Expr, inner: &Expr) -> bool {
    matches!(expr.kind, Kind::Neg) && expr.children.len() == 1 && expr_eq(&expr.children[0], inner)
}

/// One theorem-backed local rewrite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertStep {
    pub theorem: LeanTheorem,
    pub path: ExprPath,
    pub context: ExprContext,
    pub before: Arc<Expr>,
    pub after: Arc<Expr>,
}

/// End-to-end certificate for `original == simplified` at `bitwidth`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanCertificate {
    pub bitwidth: u32,
    pub original: Arc<Expr>,
    pub simplified: Arc<Expr>,
    pub steps: Vec<CertStep>,
}

/// Widths a certificate may be issued at. The `_64` pack covers 64, and the
/// width-generic pack covers everything in 1..=64; anything outside the
/// evaluator's supported range is rejected outright.
const fn is_valid_certificate_bitwidth(bitwidth: u32) -> bool {
    bitwidth >= 1 && bitwidth <= 64
}

impl LeanCertificate {
    #[must_use]
    pub fn new(bitwidth: u32, original: Arc<Expr>, simplified: Arc<Expr>) -> Self {
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
        before: Arc<Expr>,
        after: Arc<Expr>,
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
        before: Arc<Expr>,
        after: Arc<Expr>,
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
        original: Arc<Expr>,
        path: ExprPath,
        after: Arc<Expr>,
    ) -> Option<Self> {
        if !is_valid_certificate_bitwidth(bitwidth) {
            return None;
        }
        // A cast or `Concat` makes the tree non-uniform in width (empty
        // `var_widths` defaults every variable to `bitwidth`). Uniform trees
        // stay in the `Expr`/`SemEq` world; non-uniform trees are certified
        // in the `MExpr`/`SemEqW` world, and only when every node width
        // validates — a malformed tree must never reach the prover.
        let uniform =
            is_uniform_width(&original, &[], bitwidth) && is_uniform_width(&after, &[], bitwidth);
        if !uniform && validate_widths(&original, &[], bitwidth).is_err() {
            return None;
        }
        let (context, before) = context_from_path(&original, &path)?;
        let theorem = if uniform {
            let theorem = identify_rewrite_theorem_at(bitwidth, &before, &after)?;
            // Off 64, only a theorem with a width-generic counterpart is
            // citable.
            if bitwidth != 64 && !theorem.is_width_parametric() {
                return None;
            }
            theorem
        } else {
            identify_mixed_rewrite_theorem_at(bitwidth, &before, &after)?
        };
        let simplified = context.plug(after.clone_tree());
        if !uniform && validate_widths(&simplified, &[], bitwidth).is_err() {
            return None;
        }
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
    #[allow(clippy::items_after_statements, clippy::needless_pass_by_value)]
    pub fn try_single_rewrite_between_64(
        bitwidth: u32,
        original: Arc<Expr>,
        simplified: Arc<Expr>,
    ) -> Option<Self> {
        if !is_valid_certificate_bitwidth(bitwidth) {
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

    /// `true` when this certificate's claim lives in the mixed-width
    /// (`MExpr`/`SemEqW`) world rather than the uniform `Expr`/`SemEq` world.
    #[must_use]
    pub fn is_mixed(&self) -> bool {
        !is_uniform_width(&self.original, &[], self.bitwidth)
            || !is_uniform_width(&self.simplified, &[], self.bitwidth)
    }

    #[must_use]
    pub fn matches_endpoints(&self, bitwidth: u32, original: &Expr, simplified: &Expr) -> bool {
        self.bitwidth == bitwidth && *self.original == *original && *self.simplified == *simplified
    }

    /// Validate that this certificate is a continuous sequence of recognized
    /// theorem rewrites between the exact requested endpoints.
    #[must_use]
    pub fn replays_between(&self, bitwidth: u32, original: &Expr, simplified: &Expr) -> bool {
        if !self.matches_endpoints(bitwidth, original, simplified) {
            return false;
        }
        if self.steps.is_empty() {
            return *original == *simplified;
        }
        if !is_valid_certificate_bitwidth(bitwidth) {
            return false;
        }
        let uniform = is_uniform_width(original, &[], bitwidth)
            && is_uniform_width(simplified, &[], bitwidth);
        if !uniform
            && (validate_widths(original, &[], bitwidth).is_err()
                || validate_widths(simplified, &[], bitwidth).is_err())
        {
            return false;
        }

        let mut current = self.original.clone_tree();
        for step in &self.steps {
            let recognized = if uniform {
                // Off 64, every step must cite a theorem with a width-generic
                // counterpart -- otherwise the chain is not replayable at
                // this width even though each step is individually
                // recognized.
                if bitwidth != 64 && !step.theorem.is_width_parametric() {
                    return false;
                }
                identify_rewrite_theorem_at(bitwidth, &step.before, &step.after)
            } else {
                // The mixed recognizer enforces per-step width preservation,
                // matching the `decide` obligations the emitted proof
                // discharges for `MCtx.plug_preserves_sem_eq_w`.
                identify_mixed_rewrite_theorem_at(bitwidth, &step.before, &step.after)
            };
            if recognized != Some(step.theorem)
                || *step.context.plug(step.before.clone_tree()) != *current
            {
                return false;
            }
            current = step.context.plug(step.after.clone_tree());
        }
        *current == *self.simplified
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
    pub expr: Arc<Expr>,
}

impl LeanSignatureCertificate {
    #[must_use]
    pub fn new(bitwidth: u32, num_vars: u32, signature: Vec<u64>, expr: Arc<Expr>) -> Option<Self> {
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
    fn mixed_width_expr_yields_no_certificate() {
        // Soundness wall: a tree containing a cast/Concat is not uniform-width,
        // so neither single-rewrite entry point may emit a Lean certificate
        // even when the local shape would otherwise match a 64-bit theorem.
        let widened = Expr::add(Expr::zext(Expr::variable(0), 64), Expr::constant(0));
        assert!(LeanCertificate::try_single_rewrite_64(
            64,
            widened.clone_tree(),
            ExprPath(vec![]),
            widened.clone_tree(),
        )
        .is_none());
        assert!(LeanCertificate::try_single_rewrite_between_64(
            64,
            widened.clone_tree(),
            Expr::zext(Expr::variable(0), 64),
        )
        .is_none());
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
    fn replay_requires_nonempty_continuous_theorem_evidence_for_changed_output() {
        let original = Expr::add(Expr::variable(0), Expr::constant(0));
        let simplified = Expr::variable(0);
        let empty = LeanCertificate::new(64, original.clone_tree(), simplified.clone_tree());
        assert!(!empty.replays_between(64, &original, &simplified));

        let valid = LeanCertificate::try_single_rewrite_between_64(
            64,
            original.clone_tree(),
            simplified.clone_tree(),
        )
        .expect("recognized add-zero rewrite");
        assert!(valid.replays_between(64, &original, &simplified));

        let mut forged = valid;
        forged.steps[0].after = Expr::constant(1);
        assert!(!forged.replays_between(64, &original, &simplified));
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
