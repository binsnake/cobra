//! `CoBRA` MBA expression parser.
//!
//! (lower precedence number = tighter binding; `**` and unary `~`/`-` at
//! prec 1; `|` at prec 7). Variables get indices that match the
//! lexicographically-sorted unique names.

#![forbid(unsafe_code)]

pub mod ast;
pub mod eval;
pub mod postfix;
pub mod token;

pub use crate::ast::{build_ast, parse_to_ast, AstResult, MAX_VARIABLES};
pub use crate::eval::{is_linear_mba, parse_and_evaluate, ParseResult};
pub use crate::postfix::{collect_sorted_vars, to_postfix, validate_shifts_and_exponents};
pub use crate::token::{tokenize, Token, TokenType};
