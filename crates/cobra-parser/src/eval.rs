//! Direct sweep over all 2^n Boolean assignments to produce a signature
//! vector, plus the linear-MBA predicate. Ported from `ParseAndEvaluate`
//! and `IsLinearMba` in `tools/cobra-cli/ExprParser.cpp`.
//!
//! The sweep path avoids allocating the `Expr` tree — useful when you only
//! need the signature (e.g., dataset harness hot paths). Stays byte-for-
//! byte compatible with the C++ version.

use cobra_core::arith::bitmask;
use cobra_core::result::{err, CobraError, Result};

use crate::ast::MAX_VARIABLES;
use crate::postfix::{collect_sorted_vars, to_postfix, validate_shifts_and_exponents};
use crate::token::{tokenize, TokenType};

/// Matches C++ `ParseResult`.
#[derive(Clone, Debug)]
pub struct ParseResult {
    /// Signature vector of length `2^vars.len()`.
    pub sig: Vec<u64>,
    pub vars: Vec<String>,
}

/// Compact opcode for the sweep evaluator. Separate from `cobra-core::Opcode`
/// because this evaluator is built from parser tokens (which carry `<<` and
/// `**` — operations the core IR lowers away before compilation).
#[derive(Copy, Clone, Debug)]
enum SweepOp {
    PushConst,
    PushVar,
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Pow,
    Not,
    Neg,
}

#[derive(Copy, Clone, Debug)]
struct SweepInstr {
    op: SweepOp,
    operand: u64,
}

/// Full parse + sweep. Returns the signature vector and sorted variable
/// list.
#[allow(clippy::too_many_lines)]
pub fn parse_and_evaluate(input: &str, bitwidth: u32) -> Result<ParseResult> {
    if input.is_empty() {
        return Err(err(CobraError::ParseError, "empty expression"));
    }

    let tokens = tokenize(input)?;
    if tokens.is_empty() {
        return Err(err(CobraError::ParseError, "empty expression"));
    }

    let vars = collect_sorted_vars(&tokens);
    if vars.len() > MAX_VARIABLES {
        return Err(err(
            CobraError::TooManyVariables,
            format!(
                "Expression has {} variables (max {MAX_VARIABLES} before elimination)",
                vars.len()
            ),
        ));
    }

    let postfix = to_postfix(&tokens)?;
    validate_shifts_and_exponents(&postfix, bitwidth)?;

    let mask = bitmask(bitwidth);
    let mut compiled: Vec<SweepInstr> = Vec::with_capacity(postfix.len());
    let mut depth: i32 = 0;

    for tok in &postfix {
        match tok.ty {
            TokenType::Number => {
                let v: u64 = tok
                    .value
                    .parse()
                    .map_err(|_| err(CobraError::ParseError, "invalid numeric literal"))?;
                compiled.push(SweepInstr {
                    op: SweepOp::PushConst,
                    operand: v & mask,
                });
                depth += 1;
            }
            TokenType::Variable => {
                let idx = vars
                    .iter()
                    .position(|v| v == &tok.value)
                    .ok_or_else(|| err(CobraError::ParseError, "unknown variable"))?;
                compiled.push(SweepInstr {
                    op: SweepOp::PushVar,
                    operand: idx as u64,
                });
                depth += 1;
            }
            TokenType::Op => {
                if tok.is_unary {
                    if depth < 1 {
                        return Err(err(CobraError::ParseError, "malformed expression"));
                    }
                    let op = match tok.value.as_str() {
                        "~" => SweepOp::Not,
                        "neg" => SweepOp::Neg,
                        other => {
                            return Err(err(
                                CobraError::ParseError,
                                format!("unknown unary op: {other}"),
                            ));
                        }
                    };
                    compiled.push(SweepInstr { op, operand: 0 });
                } else {
                    if depth < 2 {
                        return Err(err(CobraError::ParseError, "malformed expression"));
                    }
                    depth -= 1;
                    let op = match tok.value.as_str() {
                        "+" => SweepOp::Add,
                        "-" => SweepOp::Sub,
                        "*" => SweepOp::Mul,
                        "&" => SweepOp::And,
                        "|" => SweepOp::Or,
                        "^" => SweepOp::Xor,
                        "<<" => SweepOp::Shl,
                        ">>" => SweepOp::Shr,
                        "**" => SweepOp::Pow,
                        other => {
                            return Err(err(
                                CobraError::ParseError,
                                format!("unknown binary op: {other}"),
                            ));
                        }
                    };
                    compiled.push(SweepInstr { op, operand: 0 });
                }
            }
            TokenType::LParen | TokenType::RParen => {
                return Err(err(CobraError::ParseError, "paren in postfix stream"));
            }
        }
    }

    if depth != 1 {
        return Err(err(CobraError::ParseError, "malformed expression"));
    }

    let num_vars = vars.len() as u32;
    let len = 1usize << num_vars;
    let mut sig = vec![0u64; len];
    let mut stack: Vec<u64> = Vec::with_capacity(compiled.len());
    let mut inputs = vec![0u64; num_vars as usize];

    for (i, slot) in sig.iter_mut().enumerate().take(len) {
        for (v, input) in inputs.iter_mut().enumerate().take(num_vars as usize) {
            *input = ((i >> v) & 1) as u64;
        }
        stack.clear();
        for instr in &compiled {
            match instr.op {
                SweepOp::PushConst => stack.push(instr.operand),
                SweepOp::PushVar => stack.push(inputs[instr.operand as usize] & mask),
                SweepOp::Not => {
                    let top = stack.last_mut().unwrap();
                    *top = !*top & mask;
                }
                SweepOp::Neg => {
                    let top = stack.last_mut().unwrap();
                    *top = 0u64.wrapping_sub(*top) & mask;
                }
                _ => {
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    let r = match instr.op {
                        SweepOp::Add => a.wrapping_add(b) & mask,
                        SweepOp::Sub => a.wrapping_sub(b) & mask,
                        SweepOp::Mul => a.wrapping_mul(b) & mask,
                        SweepOp::And => a & b,
                        SweepOp::Or => (a | b) & mask,
                        SweepOp::Xor => (a ^ b) & mask,
                        SweepOp::Shl => a.wrapping_shl(b as u32) & mask,
                        SweepOp::Shr => {
                            if b >= 64 {
                                0
                            } else {
                                (a >> b) & mask
                            }
                        }
                        SweepOp::Pow => {
                            let mut base = a & mask;
                            let mut exp = b;
                            let mut r = 1u64;
                            while exp > 0 {
                                if exp & 1 != 0 {
                                    r = r.wrapping_mul(base) & mask;
                                }
                                base = base.wrapping_mul(base) & mask;
                                exp >>= 1;
                            }
                            r
                        }
                        SweepOp::PushConst | SweepOp::PushVar | SweepOp::Not | SweepOp::Neg => {
                            unreachable!()
                        }
                    };
                    stack.push(r);
                }
            }
        }
        *slot = *stack.last().unwrap();
    }

    Ok(ParseResult { sig, vars })
}

/// `true` if the input has no `var * var` or `var ** anything` node —
/// i.e. it's a linear MBA in the polynomial sense. Matches C++
/// `IsLinearMba`: any parse failure or empty input also returns `true`
/// (conservative-yes).
#[must_use]
pub fn is_linear_mba(input: &str) -> bool {
    if input.is_empty() {
        return true;
    }
    let Ok(tokens) = tokenize(input) else {
        return true;
    };
    let Ok(postfix) = to_postfix(&tokens) else {
        return true;
    };

    let mut has_var: Vec<bool> = Vec::new();
    for tok in &postfix {
        match tok.ty {
            TokenType::Number => has_var.push(false),
            TokenType::Variable => has_var.push(true),
            TokenType::Op => {
                if tok.is_unary {
                    // unary ops preserve the var-dependence flag
                    continue;
                }
                if has_var.len() < 2 {
                    return true;
                }
                let rhs = has_var.pop().unwrap();
                let lhs = has_var.pop().unwrap();
                if tok.value == "*" && lhs && rhs {
                    return false;
                }
                if tok.value == "**" && lhs {
                    return false;
                }
                has_var.push(lhs || rhs);
            }
            _ => {}
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sig_eq(input: &str, bw: u32, expected: &[u64]) {
        let r = parse_and_evaluate(input, bw).unwrap();
        assert_eq!(r.sig, expected, "input={input}");
    }

    #[test]
    fn sig_vector_constants() {
        // 0 vars → length 1
        sig_eq("0", 64, &[0]);
        sig_eq("42", 64, &[42]);
    }

    #[test]
    fn sig_vector_single_var() {
        // "a" → [0, 1]
        sig_eq("a", 64, &[0, 1]);
        // "~a" at bitwidth 8 → [0xFF, 0xFE]
        sig_eq("~a", 8, &[0xFF, 0xFE]);
    }

    #[test]
    fn sig_vector_add_and_mba_identity() {
        // (x & y) + (x | y) == x + y — verify via signature equality
        let a = parse_and_evaluate("(x & y) + (x | y)", 64).unwrap();
        let b = parse_and_evaluate("x + y", 64).unwrap();
        assert_eq!(a.vars, b.vars);
        assert_eq!(a.sig, b.sig);
    }

    #[test]
    fn sig_vector_shifts_and_pow() {
        // "a << 3" == "a * 8"
        let a = parse_and_evaluate("a << 3", 64).unwrap();
        let b = parse_and_evaluate("a * 8", 64).unwrap();
        assert_eq!(a.sig, b.sig);

        // "a ** 3" on 0/1 inputs is just the signature of "a"
        let a = parse_and_evaluate("a ** 3", 64).unwrap();
        assert_eq!(a.sig, vec![0, 1]);
    }

    #[test]
    fn sig_vector_bitwidth_masking() {
        // At bitwidth 4, (a + 7) - a == 7 on any input, but we check via mask
        let a = parse_and_evaluate("a + 20", 4).unwrap();
        // 20 mod 16 = 4; (0 + 4) = 4, (1 + 4) = 5
        assert_eq!(a.sig, vec![4, 5]);
    }

    #[test]
    fn is_linear_mba_positive() {
        assert!(is_linear_mba("a + b"));
        assert!(is_linear_mba("3 * a + 5 * b"));
        assert!(is_linear_mba("(a & b) ^ (a | b)"));
        assert!(is_linear_mba("~a"));
    }

    #[test]
    fn is_linear_mba_rejects_var_times_var() {
        assert!(!is_linear_mba("a * b"));
        assert!(!is_linear_mba("a ** 2"));
        assert!(!is_linear_mba("(a + b) * c"));
    }

    #[test]
    fn is_linear_mba_is_lenient_on_parse_failure() {
        assert!(is_linear_mba(""));
        assert!(is_linear_mba("a + "));
    }
}
