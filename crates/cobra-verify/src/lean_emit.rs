//! Lean source emission helpers for generated certificates.
//!
//! These helpers are deliberately syntax-only. They do not decide whether a
//! certificate is true; they give passes and offline tooling a stable way to
//! spell Rust `Expr` trees as terms in the Lean model.

#![allow(clippy::format_push_string)]

use std::fmt::Write as _;

use crate::core::expr::{Expr, Kind};

use crate::verify::lean_cert::{
    CertStep, ContextFrame, ExprContext, LeanCertificate, LeanSignatureCertificate, LeanTheorem,
};
use crate::verify::lean_match::{
    add_with_neg_operands, not_or_add_self_add_one_operands, not_or_minus_not_operands,
    same_or_and_operands, scaled_and_or_sum_operands, xor_and_absorb_operands,
    xor_via_or_not_operands,
};

pub const MAX_SIGNATURE_CERT_ROWS: usize = 4096;

#[must_use]
/// Name to cite for `theorem` at `bitwidth`.
///
/// At 64 the `_64` pack applies. Off 64 only the width-generic pack does, so
/// cite the `_w` counterpart -- citing the `_64` name at another width emits a
/// certificate that fails to replay, which is worse than emitting none.
fn theorem_name_at(theorem: LeanTheorem, bitwidth: u32) -> &'static str {
    if bitwidth == 64 {
        theorem.lean_name()
    } else {
        theorem
            .width_parametric_lean_name()
            .unwrap_or_else(|| theorem.lean_name())
    }
}

pub fn emit_expr(expr: &Expr) -> String {
    match &expr.kind {
        Kind::Constant(value) => format!("Cobra.Expr.const {value}"),
        Kind::Variable(index) => format!("Cobra.Expr.var {index}"),
        Kind::Add => emit_binary("add", &expr.children[0], &expr.children[1]),
        Kind::Mul => emit_binary("mul", &expr.children[0], &expr.children[1]),
        Kind::And => emit_binary("band", &expr.children[0], &expr.children[1]),
        Kind::Or => emit_binary("bor", &expr.children[0], &expr.children[1]),
        Kind::Xor => emit_binary("bxor", &expr.children[0], &expr.children[1]),
        Kind::Not => format!("Cobra.Expr.bnot ({})", emit_expr(&expr.children[0])),
        Kind::Neg => format!("Cobra.Expr.neg ({})", emit_expr(&expr.children[0])),
        Kind::Shr(amount) => format!("Cobra.Expr.shr ({}) {amount}", emit_expr(&expr.children[0])),
        // Width-changing nodes have no recognized rewrite theorem; the Lean
        // certificate paths gate them out (64-bit + uniform-width only), so
        // these terms only ever appear inside emitted comments/sub-terms.
        Kind::ZExt(w) => format!("Cobra.Expr.zext ({}) {w}", emit_expr(&expr.children[0])),
        Kind::SExt(w) => format!("Cobra.Expr.sext ({}) {w}", emit_expr(&expr.children[0])),
        Kind::Trunc(w) => format!("Cobra.Expr.trunc ({}) {w}", emit_expr(&expr.children[0])),
        Kind::Concat => emit_binary("concat", &expr.children[0], &expr.children[1]),
    }
}

#[must_use]
pub fn emit_certificate_header(name: &str, cert: &LeanCertificate) -> String {
    format!(
        "theorem {name} : Cobra.Expr.SemEq {} ({}) ({}) := by",
        cert.bitwidth,
        emit_expr(&cert.original),
        emit_expr(&cert.simplified),
    )
}

/// Emit a complete Lean theorem for this certificate using fixed-width
/// bit-vector decision procedures.
///
/// This is the fallback generator path for non-local or pass-generated
/// simplifications: the certificate still records any known local rewrite
/// steps, but the final theorem is checked independently against the Lean
/// `Expr.eval` semantics. It is intentionally fixed-width and conservative;
/// callers should expect large expressions to be more expensive than local
/// theorem chains.
#[must_use]
pub fn emit_bv_decide_certificate(name: &str, cert: &LeanCertificate) -> String {
    if cert.is_mixed() {
        return emit_mixed_bv_decide_certificate(name, cert);
    }
    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&emit_certificate_header(name, cert));
    out.push('\n');
    out.push_str(&format!(
        "  -- generated certificate: bitwidth={}, steps={}\n",
        cert.bitwidth,
        cert.steps.len()
    ));
    for (index, step) in cert.steps.iter().enumerate() {
        out.push_str(&format!(
            "  -- step {index}: theorem={}, context_frames={}\n",
            theorem_name_at(step.theorem, cert.bitwidth),
            step.context.frames.len()
        ));
    }
    out.push_str("  intro env\n");
    out.push_str("  simp [Cobra.Expr.eval]\n");
    out.push_str("  try rw [Cobra.add_mul_64, Cobra.mul_add_64]\n");
    out.push_str("  try bv_decide\n\n");
    out.push_str("end Cobra.Generated\n");
    out
}

#[must_use]
pub fn emit_step_chain_certificate(name: &str, cert: &LeanCertificate) -> Option<String> {
    if cert.is_mixed() {
        return emit_mixed_step_chain_certificate(name, cert);
    }
    if cert.steps.is_empty() {
        return None;
    }

    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&emit_certificate_header(name, cert));
    out.push('\n');
    out.push_str(&format!(
        "  -- generated step-chain certificate: bitwidth={}, steps={}\n",
        cert.bitwidth,
        cert.steps.len()
    ));
    for (index, step) in cert.steps.iter().enumerate() {
        out.push_str(&format!(
            "  have h{index} : Cobra.Expr.SemEq {} (Cobra.Ctx.plug ({}) ({})) (Cobra.Ctx.plug ({}) ({})) := by\n",
            cert.bitwidth,
            emit_context(&step.context),
            emit_expr(&step.before),
            emit_context(&step.context),
            emit_expr(&step.after),
        ));
        out.push_str(&format!(
            "    -- step theorem: {}\n",
            theorem_name_at(step.theorem, cert.bitwidth)
        ));
        out.push_str("    apply Cobra.Ctx.plug_preserves_sem_eq\n");
        if let Some(proof) = emit_direct_rewrite_step_proof(cert.bitwidth, step) {
            out.push_str(&proof);
        } else {
            out.push_str("    intro env\n");
            out.push_str("    simp [Cobra.Expr.eval, Cobra.allOnes]\n");
            out.push_str("    try rw [Cobra.add_mul_64, Cobra.mul_add_64]\n");
            out.push_str("    try bv_decide\n");
        }
    }
    out.push_str("  exact ");
    out.push_str(&sem_eq_chain_expr(cert.steps.len()));
    out.push_str("\n\nend Cobra.Generated\n");
    Some(out)
}

/// Print an expression as an `MExpr` term. Unlike [`emit_expr`], every Rust
/// `Kind` — casts and `Concat` included — has a Lean constructor here.
#[must_use]
pub fn emit_mexpr(expr: &Expr) -> String {
    match &expr.kind {
        Kind::Constant(value) => format!("Cobra.MExpr.const {value}"),
        Kind::Variable(index) => format!("Cobra.MExpr.var {index}"),
        Kind::Add => emit_mbinary("add", &expr.children[0], &expr.children[1]),
        Kind::Mul => emit_mbinary("mul", &expr.children[0], &expr.children[1]),
        Kind::And => emit_mbinary("band", &expr.children[0], &expr.children[1]),
        Kind::Or => emit_mbinary("bor", &expr.children[0], &expr.children[1]),
        Kind::Xor => emit_mbinary("bxor", &expr.children[0], &expr.children[1]),
        Kind::Not => format!("Cobra.MExpr.bnot ({})", emit_mexpr(&expr.children[0])),
        Kind::Neg => format!("Cobra.MExpr.neg ({})", emit_mexpr(&expr.children[0])),
        Kind::Shr(amount) => {
            format!(
                "Cobra.MExpr.shr ({}) {amount}",
                emit_mexpr(&expr.children[0])
            )
        }
        Kind::ZExt(w) => format!("Cobra.MExpr.zext ({}) {w}", emit_mexpr(&expr.children[0])),
        Kind::SExt(w) => format!("Cobra.MExpr.sext ({}) {w}", emit_mexpr(&expr.children[0])),
        Kind::Trunc(w) => format!("Cobra.MExpr.trunc ({}) {w}", emit_mexpr(&expr.children[0])),
        Kind::Concat => emit_mbinary("concat", &expr.children[0], &expr.children[1]),
    }
}

fn emit_mbinary(kind: &str, lhs: &Expr, rhs: &Expr) -> String {
    format!(
        "Cobra.MExpr.{kind} ({}) ({})",
        emit_mexpr(lhs),
        emit_mexpr(rhs)
    )
}

#[must_use]
pub fn emit_mctx(context: &ExprContext) -> String {
    context
        .frames
        .iter()
        .fold("Cobra.MCtx.hole".to_string(), emit_mctx_frame)
}

#[allow(clippy::needless_pass_by_value)]
fn emit_mctx_frame(inner: String, frame: &ContextFrame) -> String {
    match frame {
        ContextFrame::AddL { rhs } => format!("Cobra.MCtx.addL ({inner}) ({})", emit_mexpr(rhs)),
        ContextFrame::AddR { lhs } => format!("Cobra.MCtx.addR ({}) ({inner})", emit_mexpr(lhs)),
        ContextFrame::MulL { rhs } => format!("Cobra.MCtx.mulL ({inner}) ({})", emit_mexpr(rhs)),
        ContextFrame::MulR { lhs } => format!("Cobra.MCtx.mulR ({}) ({inner})", emit_mexpr(lhs)),
        ContextFrame::AndL { rhs } => format!("Cobra.MCtx.bandL ({inner}) ({})", emit_mexpr(rhs)),
        ContextFrame::AndR { lhs } => format!("Cobra.MCtx.bandR ({}) ({inner})", emit_mexpr(lhs)),
        ContextFrame::OrL { rhs } => format!("Cobra.MCtx.borL ({inner}) ({})", emit_mexpr(rhs)),
        ContextFrame::OrR { lhs } => format!("Cobra.MCtx.borR ({}) ({inner})", emit_mexpr(lhs)),
        ContextFrame::XorL { rhs } => format!("Cobra.MCtx.bxorL ({inner}) ({})", emit_mexpr(rhs)),
        ContextFrame::XorR { lhs } => format!("Cobra.MCtx.bxorR ({}) ({inner})", emit_mexpr(lhs)),
        ContextFrame::Not => format!("Cobra.MCtx.bnot ({inner})"),
        ContextFrame::Neg => format!("Cobra.MCtx.neg ({inner})"),
        ContextFrame::Shr { amount } => format!("Cobra.MCtx.shr ({inner}) {amount}"),
        ContextFrame::ZExt { w } => format!("Cobra.MCtx.zext ({inner}) {w}"),
        ContextFrame::SExt { w } => format!("Cobra.MCtx.sext ({inner}) {w}"),
        ContextFrame::Trunc { w } => format!("Cobra.MCtx.trunc ({inner}) {w}"),
        ContextFrame::ConcatHi { lo } => {
            format!("Cobra.MCtx.concatHi ({inner}) ({})", emit_mexpr(lo))
        }
        ContextFrame::ConcatLo { hi } => {
            format!("Cobra.MCtx.concatLo ({}) ({inner})", emit_mexpr(hi))
        }
    }
}

/// Emit a mixed-width (`MExpr`-world) step-chain certificate.
///
/// Each step is plugged through `MCtx.plug_preserves_sem_eq_w`. The
/// width-preservation side condition is discharged by `decide` — widths are
/// concrete at certificate time — and the local rewrite by unfolding `evalW`
/// and handing the concrete-width bit-vector goal to `bv_decide`. The named
/// theorem is recorded per step for the in-process structural validation in
/// `replays_between`; the replayed proof is the decision procedure.
#[must_use]
pub fn emit_mixed_step_chain_certificate(name: &str, cert: &LeanCertificate) -> Option<String> {
    if cert.steps.is_empty() {
        return None;
    }
    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("set_option linter.unusedSimpArgs false\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&format!(
        "theorem {name} : Cobra.MExpr.SemEqW {} ({}) ({}) := by\n",
        cert.bitwidth,
        emit_mexpr(&cert.original),
        emit_mexpr(&cert.simplified),
    ));
    out.push_str(&format!(
        "  -- generated mixed-width step-chain certificate: bitwidth={}, steps={}\n",
        cert.bitwidth,
        cert.steps.len()
    ));
    for (index, step) in cert.steps.iter().enumerate() {
        out.push_str(&format!(
            "  have h{index} : Cobra.MExpr.SemEqW {} (Cobra.MCtx.plug ({}) ({})) (Cobra.MCtx.plug ({}) ({})) := by\n",
            cert.bitwidth,
            emit_mctx(&step.context),
            emit_mexpr(&step.before),
            emit_mctx(&step.context),
            emit_mexpr(&step.after),
        ));
        out.push_str(&format!(
            "    -- step theorem: {}\n",
            step.theorem.lean_name()
        ));
        out.push_str("    apply Cobra.MCtx.plug_preserves_sem_eq_w\n");
        out.push_str("    \u{b7} decide\n");
        out.push_str("    \u{b7} intro env\n");
        out.push_str(
            "      simp [Cobra.MExpr.evalW, Cobra.MExpr.widthOf, Cobra.maskBV, Cobra.sextBV, Cobra.signBitBV]\n",
        );
        out.push_str("      try bv_decide\n");
    }
    out.push_str("  exact ");
    out.push_str(&sem_eq_w_chain_expr(cert.steps.len()));
    out.push_str("\n\nend Cobra.Generated\n");
    Some(out)
}

fn sem_eq_w_chain_expr(steps: usize) -> String {
    fn go(index: usize, steps: usize) -> String {
        if index + 1 == steps {
            format!("h{index}")
        } else {
            format!(
                "Cobra.MExpr.SemEqW.trans h{index} ({})",
                go(index + 1, steps)
            )
        }
    }
    debug_assert!(steps > 0);
    go(0, steps)
}

/// Mixed-width endpoint fallback: state the claim under `SemEqW` and hand the
/// concrete-width goal to `bv_decide`, mirroring the uniform fallback.
#[must_use]
pub fn emit_mixed_bv_decide_certificate(name: &str, cert: &LeanCertificate) -> String {
    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("set_option linter.unusedSimpArgs false\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&format!(
        "theorem {name} : Cobra.MExpr.SemEqW {} ({}) ({}) := by\n",
        cert.bitwidth,
        emit_mexpr(&cert.original),
        emit_mexpr(&cert.simplified),
    ));
    out.push_str(&format!(
        "  -- generated mixed-width endpoint certificate: bitwidth={}, steps={}\n",
        cert.bitwidth,
        cert.steps.len()
    ));
    out.push_str("  intro env\n");
    out.push_str(
        "  simp [Cobra.MExpr.evalW, Cobra.MExpr.widthOf, Cobra.maskBV, Cobra.sextBV, Cobra.signBitBV]\n",
    );
    out.push_str("  try bv_decide\n\n");
    out.push_str("end Cobra.Generated\n");
    out
}

fn emit_direct_rewrite_step_proof(bitwidth: u32, step: &CertStep) -> Option<String> {
    let args = theorem_eval_args(bitwidth, step.theorem, &step.before)?;
    Some(format!(
        "    intro env\n    simpa [Cobra.Expr.eval, Cobra.allOnes, BitVec.sub_eq_add_neg] using {}{}\n",
        theorem_name_at(step.theorem, bitwidth),
        args
    ))
}

#[allow(
    clippy::format_collect,
    clippy::match_same_arms,
    clippy::too_many_lines
)]
fn theorem_eval_args(bitwidth: u32, theorem: LeanTheorem, before: &Expr) -> Option<String> {
    use LeanTheorem as Thm;

    let args: Vec<&Expr> = match theorem {
        Thm::Const3And1_64 => Vec::new(),
        // Complement laws: the theorem takes just `x`, read from whichever
        // operand is not the `Not`.
        Thm::AndNotSelf64 => vec![binary_child(before, KindTag::And, 0)?],
        Thm::NotAndSelf64 => vec![binary_child(before, KindTag::And, 1)?],
        Thm::OrNotSelf64 => vec![binary_child(before, KindTag::Or, 0)?],
        Thm::NotOrSelf64 => vec![binary_child(before, KindTag::Or, 1)?],
        Thm::XorNotSelf64 => vec![binary_child(before, KindTag::Xor, 0)?],
        Thm::NotXorSelf64 => vec![binary_child(before, KindTag::Xor, 1)?],
        // Absorption: `x` is the bare operand, `y` the other operand of the
        // nested node.
        Thm::AndOrAbsorb64 => {
            let x = binary_child(before, KindTag::And, 0)?;
            let inner = binary_child(before, KindTag::And, 1)?;
            vec![x, binary_child(inner, KindTag::Or, 1)?]
        }
        Thm::AndOrAbsorbRight64 => {
            let x = binary_child(before, KindTag::And, 0)?;
            let inner = binary_child(before, KindTag::And, 1)?;
            vec![x, binary_child(inner, KindTag::Or, 0)?]
        }
        Thm::OrAndAbsorb64 => {
            let x = binary_child(before, KindTag::Or, 0)?;
            let inner = binary_child(before, KindTag::Or, 1)?;
            vec![x, binary_child(inner, KindTag::And, 1)?]
        }
        Thm::OrAndAbsorbRight64 => {
            let x = binary_child(before, KindTag::Or, 0)?;
            let inner = binary_child(before, KindTag::Or, 1)?;
            vec![x, binary_child(inner, KindTag::And, 0)?]
        }
        Thm::AndOrAbsorbComm64 => {
            let x = binary_child(before, KindTag::And, 1)?;
            let inner = binary_child(before, KindTag::And, 0)?;
            vec![x, binary_child(inner, KindTag::Or, 1)?]
        }
        Thm::AndOrAbsorbCommRight64 => {
            let x = binary_child(before, KindTag::And, 1)?;
            let inner = binary_child(before, KindTag::And, 0)?;
            vec![x, binary_child(inner, KindTag::Or, 0)?]
        }
        Thm::OrAndAbsorbComm64 => {
            let x = binary_child(before, KindTag::Or, 1)?;
            let inner = binary_child(before, KindTag::Or, 0)?;
            vec![x, binary_child(inner, KindTag::And, 1)?]
        }
        Thm::OrAndAbsorbCommRight64 => {
            let x = binary_child(before, KindTag::Or, 1)?;
            let inner = binary_child(before, KindTag::Or, 0)?;
            vec![x, binary_child(inner, KindTag::And, 0)?]
        }
        // Constant reassociation: `(x op c1) op c2` supplies x, c1, c2.
        Thm::AndConstAssoc64 => {
            let inner = binary_child(before, KindTag::And, 0)?;
            vec![
                binary_child(inner, KindTag::And, 0)?,
                binary_child(inner, KindTag::And, 1)?,
                binary_child(before, KindTag::And, 1)?,
            ]
        }
        Thm::OrConstAssoc64 => {
            let inner = binary_child(before, KindTag::Or, 0)?;
            vec![
                binary_child(inner, KindTag::Or, 0)?,
                binary_child(inner, KindTag::Or, 1)?,
                binary_child(before, KindTag::Or, 1)?,
            ]
        }
        Thm::XorConstAssoc64 => {
            let inner = binary_child(before, KindTag::Xor, 0)?;
            vec![
                binary_child(inner, KindTag::Xor, 0)?,
                binary_child(inner, KindTag::Xor, 1)?,
                binary_child(before, KindTag::Xor, 1)?,
            ]
        }
        Thm::AddZero64 => vec![binary_child(before, KindTag::Add, 0)?],
        Thm::ZeroAdd64 => vec![binary_child(before, KindTag::Add, 1)?],
        Thm::MulZero64 | Thm::MulOne64 => vec![binary_child(before, KindTag::Mul, 0)?],
        Thm::ZeroMul64 | Thm::OneMul64 => vec![binary_child(before, KindTag::Mul, 1)?],
        Thm::AndSelf64 | Thm::AndZero64 | Thm::AndAllOnes64 => {
            vec![binary_child(before, KindTag::And, 0)?]
        }
        Thm::ZeroAnd64 | Thm::AllOnesAnd64 => vec![binary_child(before, KindTag::And, 1)?],
        Thm::OrSelf64 | Thm::OrZero64 | Thm::OrAllOnes64 => {
            vec![binary_child(before, KindTag::Or, 0)?]
        }
        Thm::ZeroOr64 | Thm::AllOnesOr64 => vec![binary_child(before, KindTag::Or, 1)?],
        Thm::XorSelf64 | Thm::XorZero64 | Thm::XorEqAddSubTwoMulAnd64 => {
            if theorem == Thm::XorEqAddSubTwoMulAnd64 {
                vec![
                    binary_child(before, KindTag::Xor, 0)?,
                    binary_child(before, KindTag::Xor, 1)?,
                ]
            } else {
                vec![binary_child(before, KindTag::Xor, 0)?]
            }
        }
        Thm::ZeroXor64 => vec![binary_child(before, KindTag::Xor, 1)?],
        Thm::NotNot64 => vec![unary_child(
            unary_child(before, KindTag::Not)?,
            KindTag::Not,
        )?],
        Thm::NegNeg64 => vec![unary_child(
            unary_child(before, KindTag::Neg)?,
            KindTag::Neg,
        )?],
        Thm::BnotEqNegAddAllOnes64 | Thm::BnotEqNegAddMask64 => {
            vec![unary_child(before, KindTag::Not)?]
        }
        Thm::DemorganNotAnd64 => {
            let and_node = unary_child(before, KindTag::Not)?;
            vec![
                binary_child(and_node, KindTag::And, 0)?,
                binary_child(and_node, KindTag::And, 1)?,
            ]
        }
        Thm::DemorganOrNotNot64 => vec![
            unary_child(binary_child(before, KindTag::Or, 0)?, KindTag::Not)?,
            unary_child(binary_child(before, KindTag::Or, 1)?, KindTag::Not)?,
        ],
        Thm::DemorganNotAndNotNot64 => {
            let and_node = unary_child(before, KindTag::Not)?;
            vec![
                unary_child(binary_child(and_node, KindTag::And, 0)?, KindTag::Not)?,
                unary_child(binary_child(and_node, KindTag::And, 1)?, KindTag::Not)?,
            ]
        }
        Thm::DemorganNotOr64 => {
            let or_node = unary_child(before, KindTag::Not)?;
            vec![
                binary_child(or_node, KindTag::Or, 0)?,
                binary_child(or_node, KindTag::Or, 1)?,
            ]
        }
        Thm::DemorganNotOrNotNot64 => {
            let or_node = unary_child(before, KindTag::Not)?;
            vec![
                unary_child(binary_child(or_node, KindTag::Or, 0)?, KindTag::Not)?,
                unary_child(binary_child(or_node, KindTag::Or, 1)?, KindTag::Not)?,
            ]
        }
        Thm::ShrZero64 => vec![unary_child(before, KindTag::Shr)?],
        Thm::OrSubAndEqXor64 => {
            let (or_node, and_node) = add_with_neg_operands(before)?;
            same_or_and_operands(or_node, and_node).map(|(x, y)| vec![x, y])?
        }
        Thm::AndOrSumEqAdd64 => {
            let lhs = binary_child(before, KindTag::Add, 0)?;
            let rhs = binary_child(before, KindTag::Add, 1)?;
            same_or_and_operands(lhs, rhs)
                .or_else(|| same_or_and_operands(rhs, lhs))
                .map(|(x, y)| vec![x, y])?
        }
        Thm::XorAddTwoMulAndEqAdd64 => {
            let lhs = binary_child(before, KindTag::Add, 0)?;
            let rhs = binary_child(before, KindTag::Add, 1)?;
            let xor = if matches!(lhs.kind, Kind::Xor) {
                lhs
            } else if matches!(rhs.kind, Kind::Xor) {
                rhs
            } else {
                return None;
            };
            vec![
                binary_child(xor, KindTag::Xor, 0)?,
                binary_child(xor, KindTag::Xor, 1)?,
            ]
        }
        Thm::TwoMulAndOrSumEqTwoMulAdd64 => {
            let lhs = binary_child(before, KindTag::Add, 0)?;
            let rhs = binary_child(before, KindTag::Add, 1)?;
            scaled_and_or_sum_operands(lhs, rhs, 2).map(|(x, y)| vec![x, y])?
        }
        Thm::NotOrSubNotEqAnd64 => {
            let (or_node, not_node) = add_with_neg_operands(before)?;
            not_or_minus_not_operands(or_node, not_node).map(|(x, y)| vec![x, y])?
        }
        Thm::NotOrAddSelfAddOneEqAnd64 => {
            not_or_add_self_add_one_operands(before).map(|(x, y)| vec![x, y])?
        }
        Thm::XorViaOrNot64 => xor_via_or_not_operands(before).map(|(x, y)| vec![x, y])?,
        Thm::XorAndEqAndNot64 => xor_and_absorb_operands(before).map(|(x, y)| vec![x, y])?,
        Thm::AddComm64 | Thm::MulComm64 | Thm::AndComm64 | Thm::OrComm64 | Thm::XorComm64 => {
            return None;
        }
        Thm::AddAssoc64 | Thm::MulAssoc64 | Thm::MulAdd64 | Thm::AddMul64 => return None,
        Thm::CompileSound
        | Thm::ContextPreservesSemanticEquivalence
        | Thm::RewriteStepSound
        | Thm::ChainSound => {
            return None;
        }
        // Mixed-width (`MExpr`-world) theorems never appear in a uniform
        // chain; the mixed emitter proves each step by unfolding `evalW` at
        // concrete widths instead of citing the theorem directly.
        Thm::ZextIdentityW
        | Thm::TruncIdentityW
        | Thm::SextIdentityW
        | Thm::ZextZextW
        | Thm::TruncTruncW
        | Thm::TruncZextW => return None,
    };

    Some(
        args.into_iter()
            .map(|arg| format!(" (Cobra.Expr.eval {bitwidth} env ({}))", emit_expr(arg)))
            .collect::<String>(),
    )
}

#[derive(Copy, Clone)]
enum KindTag {
    Add,
    Mul,
    And,
    Or,
    Xor,
    Not,
    Neg,
    Shr,
}

fn binary_child(expr: &Expr, kind: KindTag, index: usize) -> Option<&Expr> {
    if expr.children.len() != 2 || !matches_kind(expr, kind) {
        return None;
    }
    expr.children.get(index).map(|c| &**c)
}

fn unary_child(expr: &Expr, kind: KindTag) -> Option<&Expr> {
    if expr.children.len() != 1 || !matches_kind(expr, kind) {
        return None;
    }
    expr.children.first().map(|c| &**c)
}

fn matches_kind(expr: &Expr, kind: KindTag) -> bool {
    matches!(
        (&expr.kind, kind),
        (Kind::Add, KindTag::Add)
            | (Kind::Mul, KindTag::Mul)
            | (Kind::And, KindTag::And)
            | (Kind::Or, KindTag::Or)
            | (Kind::Xor, KindTag::Xor)
            | (Kind::Not, KindTag::Not)
            | (Kind::Neg, KindTag::Neg)
            | (Kind::Shr(_), KindTag::Shr)
    )
}

#[must_use]
pub fn emit_constant_signature_certificate(
    name: &str,
    bitwidth: u32,
    num_vars: u32,
    signature: &[u64],
    value: u64,
) -> Option<String> {
    let expected_len = 1usize.checked_shl(num_vars)?;
    if signature.len() != expected_len || signature.iter().any(|&entry| entry != value) {
        return None;
    }

    let table = signature
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&format!(
        "theorem {name} : Cobra.SignatureSpec {bitwidth} {num_vars} [{table}] (Cobra.Expr.const {value}) := by\n"
    ));
    out.push_str("  apply Cobra.const_matches_constant_signature\n");
    out.push_str("  native_decide\n\n");
    out.push_str("end Cobra.Generated\n");
    Some(out)
}

#[must_use]
pub fn emit_signature_certificate(
    name: &str,
    bitwidth: u32,
    num_vars: u32,
    signature: &[u64],
    expr: &Expr,
) -> Option<String> {
    let expected_len = 1usize.checked_shl(num_vars)?;
    if signature.len() != expected_len || expected_len > MAX_SIGNATURE_CERT_ROWS {
        return None;
    }

    let table = emit_nat_list(signature);
    let mut out = String::new();
    out.push_str("import Cobra\n\n");
    out.push_str("namespace Cobra.Generated\n\n");
    out.push_str(&format!(
        "theorem {name} : Cobra.SignatureSpec {bitwidth} {num_vars} [{table}] ({}) := by\n",
        emit_expr(expr)
    ));
    out.push_str("  intro assignment hlt\n");
    out.push_str(&format!(
        "  have hcases : {} := by omega\n",
        assignment_cases(expected_len)
    ));
    if expected_len == 1 {
        out.push_str("  rcases hcases with rfl\n");
    } else {
        out.push_str(&format!(
            "  rcases hcases with {}\n",
            std::iter::repeat_n("rfl", expected_len)
                .collect::<Vec<_>>()
                .join(" | ")
        ));
    }
    out.push_str("  all_goals native_decide\n\n");
    out.push_str("end Cobra.Generated\n");
    Some(out)
}

#[must_use]
pub fn emit_signature_certificate_model(
    name: &str,
    cert: &LeanSignatureCertificate,
) -> Option<String> {
    emit_signature_certificate(
        name,
        cert.bitwidth,
        cert.num_vars,
        &cert.signature,
        &cert.expr,
    )
}

#[must_use]
pub fn emit_context_comment(context: &ExprContext) -> String {
    format!("-- context frames: {}", context.frames.len())
}

#[must_use]
pub fn emit_context(context: &ExprContext) -> String {
    context
        .frames
        .iter()
        .fold("Cobra.Ctx.hole".to_string(), emit_context_frame)
}

fn emit_binary(kind: &str, lhs: &Expr, rhs: &Expr) -> String {
    format!(
        "Cobra.Expr.{kind} ({}) ({})",
        emit_expr(lhs),
        emit_expr(rhs)
    )
}

fn emit_nat_list(values: &[u64]) -> String {
    values
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

#[allow(clippy::items_after_statements)]
fn assignment_cases(len: usize) -> String {
    debug_assert!(len > 0);
    let mut out = String::new();
    for index in 0..len.saturating_sub(1) {
        write!(&mut out, "Or (assignment = {index}) (").expect("writing to String cannot fail");
    }
    write!(&mut out, "assignment = {}", len - 1).expect("writing to String cannot fail");
    out.extend(std::iter::repeat_n(')', len - 1));
    out
}

#[allow(clippy::items_after_statements)]
fn sem_eq_chain_expr(steps: usize) -> String {
    debug_assert!(steps > 0);
    fn go(index: usize, steps: usize) -> String {
        if index + 1 == steps {
            format!("h{index}")
        } else {
            format!("Cobra.Expr.SemEq.trans h{index} ({})", go(index + 1, steps))
        }
    }
    go(0, steps)
}

#[allow(clippy::needless_pass_by_value)]
fn emit_context_frame(inner: String, frame: &ContextFrame) -> String {
    match frame {
        ContextFrame::AddL { rhs } => format!("Cobra.Ctx.addL ({inner}) ({})", emit_expr(rhs)),
        ContextFrame::AddR { lhs } => format!("Cobra.Ctx.addR ({}) ({inner})", emit_expr(lhs)),
        ContextFrame::MulL { rhs } => format!("Cobra.Ctx.mulL ({inner}) ({})", emit_expr(rhs)),
        ContextFrame::MulR { lhs } => format!("Cobra.Ctx.mulR ({}) ({inner})", emit_expr(lhs)),
        ContextFrame::AndL { rhs } => format!("Cobra.Ctx.bandL ({inner}) ({})", emit_expr(rhs)),
        ContextFrame::AndR { lhs } => format!("Cobra.Ctx.bandR ({}) ({inner})", emit_expr(lhs)),
        ContextFrame::OrL { rhs } => format!("Cobra.Ctx.borL ({inner}) ({})", emit_expr(rhs)),
        ContextFrame::OrR { lhs } => format!("Cobra.Ctx.borR ({}) ({inner})", emit_expr(lhs)),
        ContextFrame::XorL { rhs } => format!("Cobra.Ctx.bxorL ({inner}) ({})", emit_expr(rhs)),
        ContextFrame::XorR { lhs } => format!("Cobra.Ctx.bxorR ({}) ({inner})", emit_expr(lhs)),
        ContextFrame::Not => format!("Cobra.Ctx.bnot ({inner})"),
        ContextFrame::Neg => format!("Cobra.Ctx.neg ({inner})"),
        ContextFrame::Shr { amount } => format!("Cobra.Ctx.shr ({inner}) {amount}"),
        // Cast frames only occur in mixed certificates, which route through
        // `emit_mixed_step_chain_certificate`. Emitting the MCtx names here
        // keeps this total and makes a dispatch bug fail loudly in Lean
        // rather than panicking during emission.
        ContextFrame::ZExt { w } => format!("Cobra.MCtx.zext ({inner}) {w}"),
        ContextFrame::SExt { w } => format!("Cobra.MCtx.sext ({inner}) {w}"),
        ContextFrame::Trunc { w } => format!("Cobra.MCtx.trunc ({inner}) {w}"),
        ContextFrame::ConcatHi { lo } => {
            format!("Cobra.MCtx.concatHi ({inner}) ({})", emit_mexpr(lo))
        }
        ContextFrame::ConcatLo { hi } => {
            format!("Cobra.MCtx.concatLo ({}) ({inner})", emit_mexpr(hi))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::expr::Expr;

    #[test]
    fn emits_expr_tree() {
        let expr = Expr::add(Expr::variable(0), Expr::constant(1));
        assert_eq!(
            emit_expr(&expr),
            "Cobra.Expr.add (Cobra.Expr.var 0) (Cobra.Expr.const 1)"
        );
    }

    #[test]
    fn emits_certificate_header() {
        let cert = LeanCertificate::new(64, Expr::variable(0), Expr::variable(0));
        assert_eq!(
            emit_certificate_header("same_x", &cert),
            "theorem same_x : Cobra.Expr.SemEq 64 (Cobra.Expr.var 0) (Cobra.Expr.var 0) := by"
        );
    }

    #[test]
    fn emits_complete_bv_decide_certificate() {
        let cert = LeanCertificate::new(
            64,
            Expr::add(Expr::variable(0), Expr::constant(0)),
            Expr::variable(0),
        );
        let emitted = emit_bv_decide_certificate("add_zero_cert", &cert);
        assert!(emitted.contains("import Cobra"));
        assert!(emitted.contains("theorem add_zero_cert : Cobra.Expr.SemEq 64"));
        assert!(emitted.contains("intro env"));
        assert!(emitted.contains("try bv_decide"));
        assert!(emitted.contains("end Cobra.Generated"));
    }

    #[test]
    fn emits_step_chain_certificate() {
        let cert = LeanCertificate::try_single_rewrite_64(
            64,
            Expr::add(Expr::variable(0), Expr::constant(0)),
            crate::verify::ExprPath::default(),
            Expr::variable(0),
        )
        .expect("rewrite certificate");
        let emitted = emit_step_chain_certificate("add_zero_chain", &cert).expect("chain cert");
        assert!(emitted.contains("generated step-chain certificate"));
        assert!(emitted.contains("Cobra.Ctx.plug_preserves_sem_eq"));
        assert!(emitted.contains("step theorem: Cobra.add_zero_64"));
        assert!(emitted.contains("using Cobra.add_zero_64"));
        assert!(!emitted.contains("try bv_decide"));
        assert!(emitted.contains("theorem add_zero_chain"));
    }

    #[test]
    fn emits_constant_signature_certificate() {
        let emitted =
            emit_constant_signature_certificate("const_sig", 64, 2, &[42, 42, 42, 42], 42)
                .expect("constant signature certificate");
        assert!(emitted.contains("theorem const_sig : Cobra.SignatureSpec 64 2"));
        assert!(emitted.contains("[42, 42, 42, 42]"));
        assert!(emitted.contains("Cobra.const_matches_constant_signature"));
        assert!(emit_constant_signature_certificate("bad", 64, 2, &[42, 7, 42, 42], 42).is_none());
    }

    #[test]
    fn emits_general_signature_certificate() {
        let emitted = emit_signature_certificate(
            "xor_sig",
            64,
            2,
            &[0, 1, 1, 0],
            &Expr::xor(Expr::variable(0), Expr::variable(1)),
        )
        .expect("signature certificate");
        assert!(emitted.contains("theorem xor_sig : Cobra.SignatureSpec 64 2"));
        assert!(emitted.contains("have hcases : Or (assignment = 0)"));
        assert!(emitted.contains("rcases hcases with rfl | rfl | rfl | rfl"));
        assert!(emitted.contains("all_goals native_decide"));
        assert!(
            emit_signature_certificate("bad_len", 64, 2, &[0, 1], &Expr::variable(0)).is_none()
        );
    }

    #[test]
    fn emits_signature_certificate_from_model() {
        let cert = LeanSignatureCertificate::new(
            64,
            2,
            vec![0, 1, 1, 0],
            Expr::xor(Expr::variable(0), Expr::variable(1)),
        )
        .expect("signature certificate model");
        let emitted =
            emit_signature_certificate_model("xor_sig_model", &cert).expect("emitted theorem");
        assert!(emitted.contains("theorem xor_sig_model : Cobra.SignatureSpec 64 2"));
    }

    #[test]
    fn oversized_signature_certificate_is_rejected_without_recursion() {
        let rows = MAX_SIGNATURE_CERT_ROWS * 2;
        assert!(emit_signature_certificate(
            "oversized",
            64,
            13,
            &vec![0; rows],
            &Expr::variable(0),
        )
        .is_none());
    }

    #[test]
    fn emits_context_term() {
        let context = ExprContext {
            frames: vec![
                ContextFrame::AndL {
                    rhs: Expr::constant(0),
                },
                ContextFrame::AddR {
                    lhs: Expr::variable(1),
                },
            ],
        };
        assert_eq!(
            emit_context(&context),
            "Cobra.Ctx.addR (Cobra.Expr.var 1) (Cobra.Ctx.bandL (Cobra.Ctx.hole) (Cobra.Expr.const 0))"
        );
    }
}
