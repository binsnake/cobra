//! Lean source emission helpers for generated certificates.
//!
//! These helpers are deliberately syntax-only. They do not decide whether a
//! certificate is true; they give passes and offline tooling a stable way to
//! spell Rust `Expr` trees as terms in the Lean model.

use cobra_core::expr::{Expr, Kind};

use crate::lean_cert::{ContextFrame, ExprContext, LeanCertificate, LeanSignatureCertificate};

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
    out.push_str("  try bv_decide\n\n");
    out.push_str("end Cobra.Generated\n");
    out
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
