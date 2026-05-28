//! Lean source emission helpers for generated certificates.
//!
//! These helpers are deliberately syntax-only. They do not decide whether a
//! certificate is true; they give passes and offline tooling a stable way to
//! spell Rust `Expr` trees as terms in the Lean model.

use cobra_core::expr::{Expr, Kind};

use crate::lean_cert::{
    CertStep, ContextFrame, ExprContext, LeanCertificate, LeanSignatureCertificate, LeanTheorem,
};

#[must_use]
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
            step.theorem.lean_name(),
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
            step.theorem.lean_name()
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

fn emit_direct_rewrite_step_proof(bitwidth: u32, step: &CertStep) -> Option<String> {
    let args = theorem_eval_args(bitwidth, step.theorem, &step.before)?;
    Some(format!(
        "    intro env\n    simpa [Cobra.Expr.eval, Cobra.allOnes, BitVec.sub_eq_add_neg] using {}{}\n",
        step.theorem.lean_name(),
        args
    ))
}

fn theorem_eval_args(bitwidth: u32, theorem: LeanTheorem, before: &Expr) -> Option<String> {
    use LeanTheorem as Thm;

    let args: Vec<&Expr> = match theorem {
        Thm::Const3And1_64 => Vec::new(),
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
    expr.children.get(index).map(Box::as_ref)
}

fn unary_child(expr: &Expr, kind: KindTag) -> Option<&Expr> {
    if expr.children.len() != 1 || !matches_kind(expr, kind) {
        return None;
    }
    expr.children.first().map(Box::as_ref)
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

fn add_with_neg_operands(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let lhs = binary_child(expr, KindTag::Add, 0)?;
    let rhs = binary_child(expr, KindTag::Add, 1)?;
    if matches_kind(rhs, KindTag::Neg) {
        Some((lhs, unary_child(rhs, KindTag::Neg)?))
    } else if matches_kind(lhs, KindTag::Neg) {
        Some((rhs, unary_child(lhs, KindTag::Neg)?))
    } else {
        None
    }
}

fn same_or_and_operands<'a>(or_node: &'a Expr, and_node: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
    let or_lhs = binary_child(or_node, KindTag::Or, 0)?;
    let or_rhs = binary_child(or_node, KindTag::Or, 1)?;
    let and_lhs = binary_child(and_node, KindTag::And, 0)?;
    let and_rhs = binary_child(and_node, KindTag::And, 1)?;
    if unordered_pair_eq(or_lhs, or_rhs, and_lhs, and_rhs) {
        Some((or_lhs, or_rhs))
    } else {
        None
    }
}

fn scaled_and_or_sum_operands<'a>(
    lhs: &'a Expr,
    rhs: &'a Expr,
    coeff: u64,
) -> Option<(&'a Expr, &'a Expr)> {
    let lhs = scaled_child(lhs, coeff)?;
    let rhs = scaled_child(rhs, coeff)?;
    same_or_and_operands(lhs, rhs).or_else(|| same_or_and_operands(rhs, lhs))
}

fn scaled_child(expr: &Expr, coeff: u64) -> Option<&Expr> {
    let lhs = binary_child(expr, KindTag::Mul, 0)?;
    let rhs = binary_child(expr, KindTag::Mul, 1)?;
    if is_const_value(lhs, coeff) {
        Some(rhs)
    } else if is_const_value(rhs, coeff) {
        Some(lhs)
    } else {
        None
    }
}

fn not_or_minus_not_operands<'a>(
    or_node: &'a Expr,
    not_node: &'a Expr,
) -> Option<(&'a Expr, &'a Expr)> {
    let a = unary_child(not_node, KindTag::Not)?;
    let lhs = binary_child(or_node, KindTag::Or, 0)?;
    let rhs = binary_child(or_node, KindTag::Or, 1)?;
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

    let one_idx = addends.iter().position(|a| is_const_value(a.expr, 1))?;
    let or_idx = addends
        .iter()
        .enumerate()
        .find(|(idx, a)| *idx != one_idx && matches_kind(a.expr, KindTag::Or))
        .map(|(idx, _)| idx)?;
    let a_idx = (0..3).find(|idx| *idx != one_idx && *idx != or_idx)?;

    let a = addends[a_idx].expr;
    let lhs = binary_child(addends[or_idx].expr, KindTag::Or, 0)?;
    let rhs = binary_child(addends[or_idx].expr, KindTag::Or, 1)?;
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
    let (mul_idx, or_node) = addends.iter().enumerate().find_map(|(idx, a)| {
        if idx == neg_two_idx || !a.negated || !matches_kind(a.expr, KindTag::Mul) {
            return None;
        }
        let lhs = binary_child(a.expr, KindTag::Mul, 0)?;
        let rhs = binary_child(a.expr, KindTag::Mul, 1)?;
        if is_const_value(lhs, 2) && matches_kind(rhs, KindTag::Or) {
            Some((idx, rhs))
        } else if is_const_value(rhs, 2) && matches_kind(lhs, KindTag::Or) {
            Some((idx, lhs))
        } else {
            None
        }
    })?;

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
    let lhs = binary_child(or_node, KindTag::Or, 0)?;
    let rhs = binary_child(or_node, KindTag::Or, 1)?;
    if (expr_eq(lhs, a) && is_not_of(rhs, b)) || (expr_eq(rhs, a) && is_not_of(lhs, b)) {
        Some((a, b))
    } else {
        None
    }
}

fn is_not_of(expr: &Expr, inner: &Expr) -> bool {
    matches_kind(expr, KindTag::Not)
        && expr.children.len() == 1
        && expr_eq(&expr.children[0], inner)
}

fn unordered_pair_eq(a: &Expr, b: &Expr, x: &Expr, y: &Expr) -> bool {
    (expr_eq(a, x) && expr_eq(b, y)) || (expr_eq(a, y) && expr_eq(b, x))
}

fn expr_eq(lhs: &Expr, rhs: &Expr) -> bool {
    lhs == rhs
}

fn is_const_value(expr: &Expr, value: u64) -> bool {
    matches!(expr.kind, Kind::Constant(v) if v == value)
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
    if signature.len() != expected_len {
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

fn assignment_cases(len: usize) -> String {
    debug_assert!(len > 0);
    fn go(index: usize, len: usize) -> String {
        let case = format!("assignment = {index}");
        if index + 1 == len {
            case
        } else {
            format!("Or ({case}) ({})", go(index + 1, len))
        }
    }
    go(0, len)
}

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
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::Expr;

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
            crate::ExprPath::default(),
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
