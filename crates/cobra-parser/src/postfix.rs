//! Shunting-yard conversion from the flat token stream to RPN, plus
//! validation of shift/exponent operands.
//!
//! Ported from `tools/cobra-cli/ExprParser.cpp`.

use cobra_core::result::{err, CobraError, Result};

use crate::token::{Token, TokenType};

/// Dijkstra-style shunting-yard. Matches the C++ precedence-climb rule:
/// a new operator pops from the stack while the top is an operator and
/// either (tok is right-assoc and top's prec < tok's prec) or (tok is
/// left-assoc and top's prec <= tok's prec).
pub fn to_postfix(tokens: &[Token]) -> Result<Vec<Token>> {
    let mut output: Vec<Token> = Vec::with_capacity(tokens.len());
    let mut ops: Vec<Token> = Vec::new();

    for tok in tokens {
        match tok.ty {
            TokenType::Number | TokenType::Variable => output.push(tok.clone()),
            TokenType::Op => {
                while let Some(top) = ops.last() {
                    if top.ty != TokenType::Op {
                        break;
                    }
                    let should_pop = if tok.right_assoc {
                        top.precedence < tok.precedence
                    } else {
                        top.precedence <= tok.precedence
                    };
                    if !should_pop {
                        break;
                    }
                    output.push(ops.pop().unwrap());
                }
                ops.push(tok.clone());
            }
            TokenType::LParen => ops.push(tok.clone()),
            TokenType::RParen => loop {
                match ops.last() {
                    Some(t) if t.ty == TokenType::LParen => {
                        ops.pop();
                        break;
                    }
                    Some(_) => output.push(ops.pop().unwrap()),
                    None => {
                        return Err(err(CobraError::ParseError, "mismatched parentheses"));
                    }
                }
            },
        }
    }

    while let Some(top) = ops.pop() {
        if top.ty == TokenType::LParen {
            return Err(err(CobraError::ParseError, "mismatched parentheses"));
        }
        output.push(top);
    }
    Ok(output)
}

/// Enforce that shift amounts and power exponents are integer literals and
/// (for shifts) fit within `bitwidth`. Mirrors
/// `ValidateShiftsAndExponents`.
pub fn validate_shifts_and_exponents(postfix: &[Token], bitwidth: u32) -> Result<()> {
    for (i, tok) in postfix.iter().enumerate() {
        if tok.ty != TokenType::Op {
            continue;
        }
        match tok.value.as_str() {
            "<<" | ">>" => {
                let prev = postfix
                    .get(i.wrapping_sub(1))
                    .filter(|_| i > 0)
                    .filter(|p| p.ty == TokenType::Number);
                let Some(p) = prev else {
                    return Err(err(
                        CobraError::ParseError,
                        "unsupported: shift amount must be an integer literal",
                    ));
                };
                let k: u64 = p
                    .value
                    .parse()
                    .map_err(|_| err(CobraError::ParseError, "invalid shift amount literal"))?;
                if k >= u64::from(bitwidth) {
                    return Err(err(
                        CobraError::ParseError,
                        format!("shift amount {k} out of range for {bitwidth}-bit mode"),
                    ));
                }
            }
            "**" => {
                let prev = postfix
                    .get(i.wrapping_sub(1))
                    .filter(|_| i > 0)
                    .filter(|p| p.ty == TokenType::Number);
                if prev.is_none() {
                    return Err(err(
                        CobraError::ParseError,
                        "unsupported: exponent must be an integer literal",
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Unique, lexicographically-sorted variable names appearing in `tokens`.
#[must_use]
pub fn collect_sorted_vars(tokens: &[Token]) -> Vec<String> {
    let mut set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for t in tokens {
        if t.ty == TokenType::Variable {
            set.insert(t.value.clone());
        }
    }
    set.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::tokenize;

    fn rpn(input: &str) -> Vec<String> {
        let toks = tokenize(input).unwrap();
        let post = to_postfix(&toks).unwrap();
        post.into_iter().map(|t| t.value).collect()
    }

    #[test]
    fn shunting_yard_simple() {
        assert_eq!(rpn("a + b"), vec!["a", "b", "+"]);
        assert_eq!(rpn("a + b * c"), vec!["a", "b", "c", "*", "+"]);
        assert_eq!(rpn("(a + b) * c"), vec!["a", "b", "+", "c", "*"]);
    }

    #[test]
    fn shunting_yard_chain_is_left_assoc() {
        // + is left-assoc at prec 3 → (a + b) + c → "a b + c +"
        assert_eq!(rpn("a + b + c"), vec!["a", "b", "+", "c", "+"]);
    }

    #[test]
    fn shunting_yard_right_assoc_exponent() {
        // ** is right-assoc at prec 1. "a ** 2 ** 3" → "a 2 3 ** **"
        assert_eq!(rpn("a ** 2 ** 3"), vec!["a", "2", "3", "**", "**"]);
    }

    #[test]
    fn shunting_yard_unary_after_binop() {
        // "a + -b" → "a b neg +" — neg is right-assoc prec 1, binds tightly
        assert_eq!(rpn("a + -b"), vec!["a", "b", "neg", "+"]);
    }

    #[test]
    fn shunting_yard_mismatched_paren_right() {
        let toks = tokenize("a + b)").unwrap();
        let e = to_postfix(&toks).unwrap_err();
        assert!(e.message.contains("mismatched"));
    }

    #[test]
    fn shunting_yard_mismatched_paren_left() {
        let toks = tokenize("(a + b").unwrap();
        let e = to_postfix(&toks).unwrap_err();
        assert!(e.message.contains("mismatched"));
    }

    #[test]
    fn validate_shift_amount_literal_required() {
        let toks = tokenize("a << b").unwrap();
        let post = to_postfix(&toks).unwrap();
        let e = validate_shifts_and_exponents(&post, 64).unwrap_err();
        assert!(e.message.contains("shift amount must be"));
    }

    #[test]
    fn validate_shift_amount_in_range() {
        let toks = tokenize("a << 3").unwrap();
        let post = to_postfix(&toks).unwrap();
        validate_shifts_and_exponents(&post, 64).unwrap();
    }

    #[test]
    fn validate_shift_amount_out_of_range() {
        let toks = tokenize("a << 8").unwrap();
        let post = to_postfix(&toks).unwrap();
        let e = validate_shifts_and_exponents(&post, 8).unwrap_err();
        assert!(e.message.contains("out of range"));
    }

    #[test]
    fn validate_exponent_literal_required() {
        let toks = tokenize("a ** b").unwrap();
        let post = to_postfix(&toks).unwrap();
        let e = validate_shifts_and_exponents(&post, 64).unwrap_err();
        assert!(e.message.contains("exponent must be"));
    }

    #[test]
    fn collect_sorted_vars_is_lex_sorted_and_unique() {
        let toks = tokenize("c + a + b + a + ab").unwrap();
        let v = collect_sorted_vars(&toks);
        assert_eq!(
            v,
            vec![
                "a".to_owned(),
                "ab".to_owned(),
                "b".to_owned(),
                "c".to_owned()
            ]
        );
    }
}
