//! Public API for the `CoBRA` mixed Boolean-arithmetic simplifier.
//!
//! The package emits both a normal Rust `rlib` and a Rust `dylib`. Static
//! linking remains the default; development builds can select the DLL with
//! `RUSTFLAGS="-C prefer-dynamic"` to reduce relinking in consumers.
//!
//! ```toml
//! [dependencies]
//! cobra = { package = "cobra-mba", version = "0.4" }
//! ```
//!
//! ```rust
//! use cobra::{parse_to_ast, render, simplify_expr, Options};
//!
//! let parsed = parse_to_ast("(x ^ y) + 2 * (x & y)", 64)?;
//! let outcome = simplify_expr(&parsed.expr, &parsed.vars, Options::default())?;
//! let simplified = outcome.expr.as_deref().unwrap_or(&parsed.expr);
//! assert_eq!(render(simplified, &parsed.vars, 64), "x + y");
//! # Ok::<(), cobra::ErrorInfo>(())
//! ```

#![forbid(unsafe_code)]

// The implementation remains split into focused source trees, but all of
// these modules are compiled and published as one Cargo package.
#[path = "../../cobra-core/src/lib.rs"]
pub mod core;
#[path = "../../cobra-ir/src/lib.rs"]
pub mod ir;
#[path = "../../cobra-orchestrator/src/lib.rs"]
pub mod orchestrator;
#[path = "../../cobra-parser/src/lib.rs"]
pub mod parser;
#[path = "../../cobra-passes/src/lib.rs"]
pub mod passes;
#[path = "../../cobra-simd/src/lib.rs"]
pub mod simd;
#[doc(hidden)]
#[path = "../../cobra-testkit/src/lib.rs"]
pub mod testkit;
#[path = "../../cobra-verify/src/lib.rs"]
pub mod verify;

/// Expression types and rendering helpers.
pub mod expression {
    pub use crate::core::expr::{render, Expr, Kind};
    pub use crate::core::expr_rewrite::build_var_support;
    pub use crate::core::expr_utils::remap_var_indices;
}

/// Simplifier entry points, options, outcomes, and diagnostics.
pub mod simplify {
    pub use crate::core::simplify_outcome::{
        Diagnostic, Options, ProofLevel, SimplifyOutcome, SimplifyOutcomeKind, SimplifyTelemetry,
    };
    pub use crate::passes::{simplify, simplify_expr, MAX_INPUT_VARS};
}

/// Map a finished outcome's expression back into the caller's variable
/// namespace.
///
/// A result that dropped variables is indexed against
/// [`SimplifyOutcome::real_vars`], not the table the caller passed in, so
/// rendering it against the caller's table without this step prints the wrong
/// names. Returns `None` when the outcome carries no expression.
#[must_use]
pub fn outcome_expr_in_original_space(
    outcome: &SimplifyOutcome,
    original_vars: &[String],
) -> Option<std::sync::Arc<Expr>> {
    let mut owned = outcome.expr.as_ref()?.clone();
    if !outcome.real_vars.is_empty() && outcome.real_vars.len() < original_vars.len() {
        if let Some(index_map) =
            crate::core::expr_rewrite::try_build_var_support(original_vars, &outcome.real_vars)
        {
            remap_var_indices(std::sync::Arc::make_mut(&mut owned), &index_map);
        }
    }
    Some(owned)
}

pub use crate::core::{is_valid_bitwidth, CobraError, ErrorInfo, Result};
pub use crate::expression::{build_var_support, remap_var_indices, render, Expr, Kind};
pub use crate::parser::{parse_to_ast, AstResult, MAX_VARIABLES};
pub use crate::simplify::{
    simplify, simplify_expr, Diagnostic, Options, ProofLevel, SimplifyOutcome, SimplifyOutcomeKind,
    SimplifyTelemetry, MAX_INPUT_VARS,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_api_simplifies_an_expression() {
        let parsed = parse_to_ast("(x ^ y) + 2 * (x & y)", 64).expect("parse input");
        let outcome =
            simplify_expr(&parsed.expr, &parsed.vars, Options::default()).expect("simplify input");
        let simplified = outcome.expr.as_deref().unwrap_or(&parsed.expr);

        assert_eq!(render(simplified, &parsed.vars, 64), "x + y");
    }
}
