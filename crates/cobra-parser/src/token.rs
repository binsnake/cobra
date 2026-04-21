//! Token stream for the MBA expression grammar.
//!
//! Ported from the anonymous-namespace helpers in
//! `tools/cobra-cli/ExprParser.cpp`. Tokens carry both precedence and
//! right-associativity so that the shunting-yard stage does not have to
//! look anything up — the lexer is the single source of truth for the
//! operator table.

use cobra_core::result::{err, CobraError, Result};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenType {
    Number,
    Variable,
    Op,
    LParen,
    RParen,
}

/// Parsed token. The `value` field holds:
/// - decimal string for `Number` (hex inputs are converted to decimal here),
/// - identifier text for `Variable`,
/// - operator symbol for `Op` (`+`, `-`, `*`, `&`, `|`, `^`, `~`, `**`,
///   `<<`, `>>`, or the sentinel `neg` for unary minus),
/// - `(` or `)` for paren tokens.
///
/// `precedence` / `right_assoc` / `is_unary` are only meaningful on `Op`
/// tokens. Matching the C++ `Token` struct exactly so the shunting-yard
/// translation is line-for-line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub ty: TokenType,
    pub value: String,
    pub precedence: i32,
    pub right_assoc: bool,
    pub is_unary: bool,
}

impl Token {
    fn op(value: &str, precedence: i32, right_assoc: bool, is_unary: bool) -> Self {
        Self {
            ty: TokenType::Op,
            value: value.to_owned(),
            precedence,
            right_assoc,
            is_unary,
        }
    }

    fn number(value: String) -> Self {
        Self {
            ty: TokenType::Number,
            value,
            precedence: 0,
            right_assoc: false,
            is_unary: false,
        }
    }

    fn variable(value: String) -> Self {
        Self {
            ty: TokenType::Variable,
            value,
            precedence: 0,
            right_assoc: false,
            is_unary: false,
        }
    }

    fn lparen() -> Self {
        Self {
            ty: TokenType::LParen,
            value: "(".to_owned(),
            precedence: 0,
            right_assoc: false,
            is_unary: false,
        }
    }

    fn rparen() -> Self {
        Self {
            ty: TokenType::RParen,
            value: ")".to_owned(),
            precedence: 0,
            right_assoc: false,
            is_unary: false,
        }
    }
}

/// Tokenize the input string. Consumes bytes, not chars — matches the C++
/// implementation which uses `std::isspace`/`std::isdigit` on single bytes.
/// Identifier characters follow ASCII `[A-Za-z_][A-Za-z0-9_]*`.
#[allow(clippy::too_many_lines)]
pub fn tokenize(input: &str) -> Result<Vec<Token>> {
    let bytes = input.as_bytes();
    let mut tokens: Vec<Token> = Vec::new();
    let mut i = 0;

    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }

        // Hex literal: 0x... / 0X...
        if c == b'0' && i + 1 < bytes.len() && (bytes[i + 1] == b'x' || bytes[i + 1] == b'X') {
            i += 2;
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_hexdigit() {
                i += 1;
            }
            if i == start {
                return Err(err(
                    CobraError::ParseError,
                    format!("empty hex literal at position {}", i - 2),
                ));
            }
            let digits = std::str::from_utf8(&bytes[start..i]).expect("ascii hex digits");
            let val = u64::from_str_radix(digits, 16).map_err(|_| {
                err(
                    CobraError::ParseError,
                    format!("hex literal out of 64-bit range at position {}", start - 2),
                )
            })?;
            tokens.push(Token::number(val.to_string()));
            continue;
        }

        // Decimal literal
        if c.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let digits = std::str::from_utf8(&bytes[start..i]).expect("ascii digits");
            tokens.push(Token::number(digits.to_owned()));
            continue;
        }

        // Identifier: [A-Za-z_][A-Za-z0-9_]*
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let name = std::str::from_utf8(&bytes[start..i]).expect("ascii identifier");
            tokens.push(Token::variable(name.to_owned()));
            continue;
        }

        if c == b'(' {
            tokens.push(Token::lparen());
            i += 1;
            continue;
        }
        if c == b')' {
            tokens.push(Token::rparen());
            i += 1;
            continue;
        }

        // Two-character operators: **, <<, >>
        if c == b'*' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            tokens.push(Token::op("**", 1, true, false));
            i += 2;
            continue;
        }
        if c == b'<' && i + 1 < bytes.len() && bytes[i + 1] == b'<' {
            tokens.push(Token::op("<<", 4, false, false));
            i += 2;
            continue;
        }
        if c == b'>' && i + 1 < bytes.len() && bytes[i + 1] == b'>' {
            tokens.push(Token::op(">>", 4, false, false));
            i += 2;
            continue;
        }

        // Unary / single-character operators
        let could_be_unary = tokens
            .last()
            .is_none_or(|t| matches!(t.ty, TokenType::Op | TokenType::LParen));

        if c == b'~' {
            tokens.push(Token::op("~", 1, true, true));
            i += 1;
            continue;
        }
        if c == b'-' && could_be_unary {
            tokens.push(Token::op("neg", 1, true, true));
            i += 1;
            continue;
        }

        let prec = match c {
            b'*' => 2,
            b'+' | b'-' => 3,
            b'&' => 5,
            b'^' => 6,
            b'|' => 7,
            _ => {
                return Err(err(
                    CobraError::ParseError,
                    format!("unexpected character '{}' at position {}", c as char, i),
                ));
            }
        };
        tokens.push(Token::op(&(c as char).to_string(), prec, false, false));
        i += 1;
    }

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn types(toks: &[Token]) -> Vec<TokenType> {
        toks.iter().map(|t| t.ty).collect()
    }

    fn values(toks: &[Token]) -> Vec<&str> {
        toks.iter().map(|t| t.value.as_str()).collect()
    }

    #[test]
    fn tokenize_empty_is_empty() {
        let toks = tokenize("").unwrap();
        assert!(toks.is_empty());
    }

    #[test]
    fn tokenize_decimal_and_hex() {
        let toks = tokenize("42 0xFF 0xdeadbeef 7").unwrap();
        assert_eq!(types(&toks), vec![TokenType::Number; 4]);
        assert_eq!(values(&toks), vec!["42", "255", "3735928559", "7"]);
    }

    #[test]
    fn tokenize_identifier_rules() {
        let toks = tokenize("a b0 _foo aB_1 x").unwrap();
        assert_eq!(types(&toks), vec![TokenType::Variable; 5]);
        assert_eq!(values(&toks), vec!["a", "b0", "_foo", "aB_1", "x"]);
    }

    #[test]
    fn tokenize_two_char_ops() {
        let toks = tokenize("a ** b << 3 >> c").unwrap();
        let ops: Vec<&str> = toks
            .iter()
            .filter(|t| t.ty == TokenType::Op)
            .map(|t| t.value.as_str())
            .collect();
        assert_eq!(ops, vec!["**", "<<", ">>"]);
    }

    #[test]
    fn tokenize_unary_minus_at_start_and_after_lparen() {
        let toks = tokenize("-a").unwrap();
        assert_eq!(toks[0].value, "neg");
        assert!(toks[0].is_unary);

        let toks = tokenize("(-a)").unwrap();
        assert_eq!(toks[1].value, "neg");
        assert!(toks[1].is_unary);
    }

    #[test]
    fn tokenize_binary_minus_after_operand() {
        let toks = tokenize("a - b").unwrap();
        // Three tokens: Var, Op '-', Var
        assert_eq!(toks.len(), 3);
        assert_eq!(toks[1].value, "-");
        assert_eq!(toks[1].precedence, 3);
        assert!(!toks[1].is_unary);
    }

    #[test]
    fn tokenize_operator_precedences() {
        // Lifted from the C++ operator table: lower number = tighter binding.
        let cases = [
            ("~", 1, true, true),
            ("*", 2, false, false),
            ("+", 3, false, false),
            ("-", 3, false, false), // binary
            ("<<", 4, false, false),
            (">>", 4, false, false),
            ("&", 5, false, false),
            ("^", 6, false, false),
            ("|", 7, false, false),
            ("**", 1, true, false),
        ];
        for (op, prec, right, unary) in cases {
            // Build an input that forces binary context for `-`, `+`, etc.
            let input: String = if op == "~" {
                "~a".to_owned()
            } else if op == "**" {
                "a ** 3".to_owned()
            } else {
                format!("a {op} b")
            };
            let toks = tokenize(&input).unwrap();
            let t = toks
                .iter()
                .find(|t| t.ty == TokenType::Op && t.value == op)
                .expect("operator present");
            assert_eq!(t.precedence, prec, "op={op}");
            assert_eq!(t.right_assoc, right, "op={op}");
            assert_eq!(t.is_unary, unary, "op={op}");
        }
    }

    #[test]
    fn tokenize_parens() {
        let toks = tokenize("(a)").unwrap();
        assert_eq!(
            types(&toks),
            vec![TokenType::LParen, TokenType::Variable, TokenType::RParen]
        );
    }

    #[test]
    fn tokenize_rejects_unexpected_char() {
        let e = tokenize("a % b").unwrap_err();
        assert_eq!(e.code, CobraError::ParseError);
        assert!(e.message.contains("unexpected character"));
    }

    #[test]
    fn tokenize_rejects_empty_hex_literal() {
        let e = tokenize("0x ").unwrap_err();
        assert!(e.message.contains("empty hex literal"));
    }

    #[test]
    fn tokenize_rejects_hex_overflow() {
        // 17 hex digits guarantees overflow past u64
        let e = tokenize("0xFFFFFFFFFFFFFFFFF").unwrap_err();
        assert!(e.message.contains("out of 64-bit range"));
    }
}
