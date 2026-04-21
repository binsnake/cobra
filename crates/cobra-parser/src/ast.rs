//! Postfix → `Expr` tree conversion plus the top-level
//! [`parse_to_ast`] entry point.
//!
//! Ported from `BuildAstFromPostfix` and `ParseToAst` in
//! `tools/cobra-cli/ExprParser.cpp`.

use cobra_core::arith::bitmask;
use cobra_core::expr::{Expr, Kind};
use cobra_core::result::{err, CobraError, Result};

use crate::postfix::{collect_sorted_vars, to_postfix, validate_shifts_and_exponents};
use crate::token::{Token, TokenType};

/// Matches C++ `AstResult`.
#[derive(Clone, Debug)]
pub struct AstResult {
    pub expr: Box<Expr>,
    pub vars: Vec<String>,
}

/// Maximum variable count enforced by the parser (matches C++ 20-var cap).
pub const MAX_VARIABLES: usize = 20;

/// Parse an MBA expression string into an `Expr` tree. Variables are
/// extracted and sorted lexicographically; variable indices correspond to
/// positions in the sorted `vars` list. Constants are masked to
/// `bitmask(bitwidth)`.
pub fn parse_to_ast(input: &str, bitwidth: u32) -> Result<AstResult> {
    if input.is_empty() {
        return Err(err(CobraError::ParseError, "empty expression"));
    }

    let tokens = crate::token::tokenize(input)?;
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
    let expr = build_ast(&postfix, &vars, bitwidth)?;
    Ok(AstResult { expr, vars })
}

/// Reconstruct an `Expr` tree from a postfix token sequence. `var_names` is
/// the sorted variable list produced by [`collect_sorted_vars`].
pub fn build_ast(postfix: &[Token], var_names: &[String], bitwidth: u32) -> Result<Box<Expr>> {
    let mask = bitmask(bitwidth);
    let mut stack: Vec<Box<Expr>> = Vec::new();

    for tok in postfix {
        match tok.ty {
            TokenType::Number => {
                let num: u64 = tok.value.parse().map_err(|_| {
                    err(
                        CobraError::ParseError,
                        format!("invalid numeric literal '{}'", tok.value),
                    )
                })?;
                stack.push(Expr::constant(num & mask));
            }
            TokenType::Variable => {
                let idx = var_names
                    .iter()
                    .position(|v| v == &tok.value)
                    .ok_or_else(|| err(CobraError::ParseError, "unknown variable"))?;
                stack.push(Expr::variable(idx as u32));
            }
            TokenType::Op => {
                if tok.is_unary {
                    let operand = stack
                        .pop()
                        .ok_or_else(|| err(CobraError::ParseError, "malformed expression"))?;
                    match tok.value.as_str() {
                        "~" => stack.push(Expr::not(operand)),
                        "neg" => stack.push(Expr::neg(operand)),
                        other => {
                            return Err(err(
                                CobraError::ParseError,
                                format!("unknown unary op: {other}"),
                            ));
                        }
                    }
                } else {
                    if stack.len() < 2 {
                        return Err(err(CobraError::ParseError, "malformed expression"));
                    }
                    let rhs = stack.pop().unwrap();
                    let lhs = stack.pop().unwrap();
                    match tok.value.as_str() {
                        "**" => stack.push(apply_pow(lhs, &rhs, mask)?),
                        "<<" => stack.push(apply_shl(lhs, &rhs, mask)?),
                        ">>" => stack.push(apply_shr(lhs, &rhs)?),
                        "+" => stack.push(Expr::add(lhs, rhs)),
                        "-" => stack.push(Expr::add(lhs, Expr::neg(rhs))),
                        "*" => stack.push(Expr::mul(lhs, rhs)),
                        "&" => stack.push(Expr::and(lhs, rhs)),
                        "|" => stack.push(Expr::or(lhs, rhs)),
                        "^" => stack.push(Expr::xor(lhs, rhs)),
                        other => {
                            return Err(err(
                                CobraError::ParseError,
                                format!("unknown binary op: {other}"),
                            ));
                        }
                    }
                }
            }
            TokenType::LParen | TokenType::RParen => {
                return Err(err(CobraError::ParseError, "paren in postfix stream"));
            }
        }
    }

    if stack.len() != 1 {
        return Err(err(CobraError::ParseError, "malformed expression"));
    }
    Ok(stack.pop().unwrap())
}

fn expect_constant(expr: &Expr, msg: &str) -> Result<u64> {
    match &expr.kind {
        Kind::Constant(v) => Ok(*v),
        _ => Err(err(CobraError::ParseError, msg)),
    }
}

fn apply_pow(lhs: Box<Expr>, rhs: &Expr, mask: u64) -> Result<Box<Expr>> {
    let exp = expect_constant(rhs, "unsupported: exponent must be an integer literal")?;
    if exp == 0 {
        return Ok(Expr::constant(1 & mask));
    }
    if exp == 1 {
        return Ok(lhs);
    }
    let mut result = lhs.clone_tree();
    for _ in 2..=exp {
        result = Expr::mul(result, lhs.clone_tree());
    }
    Ok(result)
}

fn apply_shl(lhs: Box<Expr>, rhs: &Expr, mask: u64) -> Result<Box<Expr>> {
    let k = expect_constant(rhs, "unsupported: shift amount must be an integer literal")?;
    // validate_shifts_and_exponents has already confirmed k < bitwidth.
    let multiplier = (1u64 << k) & mask;
    Ok(Expr::mul(lhs, Expr::constant(multiplier)))
}

fn apply_shr(lhs: Box<Expr>, rhs: &Expr) -> Result<Box<Expr>> {
    let k = expect_constant(rhs, "unsupported: shift amount must be an integer literal")?;
    Ok(Expr::shr(lhs, k))
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::expr::{render, Kind};

    fn render_parsed(input: &str, bitwidth: u32) -> String {
        let r = parse_to_ast(input, bitwidth).unwrap();
        render(&r.expr, &r.vars, bitwidth)
    }

    #[test]
    fn parse_bare_variable() {
        let r = parse_to_ast("a", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Variable(0)));
        assert_eq!(r.vars, vec!["a".to_owned()]);
    }

    #[test]
    fn parse_constant_masked() {
        let r = parse_to_ast("0xDEAD", 8).unwrap();
        assert!(matches!(r.expr.kind, Kind::Constant(0xAD)));
    }

    #[test]
    fn parse_variable_indices_follow_sorted_names() {
        let r = parse_to_ast("c + a + b", 64).unwrap();
        assert_eq!(r.vars, vec!["a".to_owned(), "b".to_owned(), "c".to_owned()]);
        // Rendered should echo the tree, not the input order.
        // (a + c) + b after shunting — left-assoc, so ((c + a) + b).
        // In index terms: Add(Add(Var(2), Var(0)), Var(1)).
        let s = render(&r.expr, &r.vars, 64);
        assert_eq!(s, "c + a + b");
    }

    #[test]
    fn parse_precedence() {
        assert_eq!(render_parsed("a + b * c", 64), "a + b * c");
        assert_eq!(render_parsed("(a + b) * c", 64), "(a + b) * c");
        assert_eq!(render_parsed("a | b & c", 64), "a | b & c");
    }

    #[test]
    fn parse_unary_minus() {
        // -a + b → Add(Neg(a), b)
        let r = parse_to_ast("-a + b", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Add));
        assert!(matches!(r.expr.children[0].kind, Kind::Neg));
    }

    #[test]
    fn parse_binary_minus_lowers_to_add_neg() {
        // a - b → Add(a, Neg(b))
        let r = parse_to_ast("a - b", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Add));
        assert!(matches!(r.expr.children[1].kind, Kind::Neg));
    }

    #[test]
    fn parse_shl_lowers_to_mul() {
        let r = parse_to_ast("a << 3", 64).unwrap();
        // Result is Mul(a, Constant(8))
        assert!(matches!(r.expr.kind, Kind::Mul));
        if let Kind::Constant(v) = r.expr.children[1].kind {
            assert_eq!(v, 8);
        } else {
            panic!("expected constant rhs");
        }
    }

    #[test]
    fn parse_shr_produces_shr_kind() {
        let r = parse_to_ast("a >> 2", 64).unwrap();
        match r.expr.kind {
            Kind::Shr(k) => assert_eq!(k, 2),
            _ => panic!("expected Shr"),
        }
    }

    #[test]
    fn parse_pow_expands_to_repeated_mul() {
        // a ** 3 → (a * a) * a
        let r = parse_to_ast("a ** 3", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Mul));
        assert!(matches!(r.expr.children[0].kind, Kind::Mul));
    }

    #[test]
    fn parse_pow_zero_is_one() {
        let r = parse_to_ast("a ** 0", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Constant(1)));
    }

    #[test]
    fn parse_pow_one_is_base() {
        let r = parse_to_ast("a ** 1", 64).unwrap();
        assert!(matches!(r.expr.kind, Kind::Variable(0)));
    }

    #[test]
    fn parse_rejects_empty_input() {
        let e = parse_to_ast("", 64).unwrap_err();
        assert!(e.message.contains("empty"));
        let e = parse_to_ast("   ", 64).unwrap_err();
        assert!(e.message.contains("empty"));
    }

    #[test]
    fn parse_rejects_too_many_variables() {
        // Build an input with 21 distinct single-letter/prefixed variables.
        let names: Vec<String> = (0..21).map(|i| format!("v{i}")).collect();
        let expr = names.join(" + ");
        let e = parse_to_ast(&expr, 64).unwrap_err();
        assert_eq!(e.code, CobraError::TooManyVariables);
    }

    #[test]
    fn parse_readme_example_1() {
        // "(x&y)+(x|y)" at bitwidth 64 parses.
        let r = parse_to_ast("(x&y)+(x|y)", 64).unwrap();
        assert_eq!(r.vars, vec!["x".to_owned(), "y".to_owned()]);
        assert!(matches!(r.expr.kind, Kind::Add));
    }
}
