//! Foundation crate for the `CoBRA` Rust port.
//!
//! Provides the expression IR (`expr`), modular arithmetic helpers
//! (`arith`), compiled stack-machine bytecode (`compiled`), and a
//! type-erased `Evaluator`. Downstream crates (`cobra-ir`, `cobra-passes`,
//! `cobra-orchestrator`, etc.) build on top of these types.

#![forbid(unsafe_code)]
// `Expr` factories intentionally return `Box<Expr>` to mirror C++
// `std::unique_ptr<Expr>` ownership semantics: callers pass trees around
// as pointers so that deep trees don't have to be moved by value.
#![allow(clippy::unnecessary_box_returns)]
// Factory methods on `Expr` (`add`, `mul`, `not`, `neg`, `shr`) are named
// after the corresponding C++ `Expr::Add` / `Expr::Negate` / etc.; they are
// constructors, not `std::ops` trait impls.
#![allow(clippy::should_implement_trait)]

pub mod arith;
pub mod classification;
pub mod compiled;
pub mod evaluator;
pub mod expr;
pub mod expr_cost;
pub mod expr_rewrite;
pub mod expr_utils;
pub mod pass_contract;
pub mod result;
pub mod signature_eval;
pub mod simplify_outcome;
pub mod spot_check;

pub use crate::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr, mod_sub};
pub use crate::classification::{
    is_folded_ast_exploration_candidate, needs_structural_recovery, Classification, SemanticClass,
    StructuralFlag,
};
pub use crate::compiled::{compile, eval, CompiledExpr, EvalInstr, Opcode};
pub use crate::evaluator::{Evaluator, TraceKind, Workspace};
pub use crate::expr::{render, Expr, Kind};
pub use crate::expr_cost::{compute_cost, is_better, CostInfo, ExprCost};
pub use crate::expr_rewrite::{
    apply_coefficient, build_and_product, build_var_support, cleanup_final_expr,
    has_nonleaf_bitwise, repair_product_shadow, try_build_var_support,
};
pub use crate::expr_utils::{
    collect_vars, eval_constant, has_var_dep, is_constant_subtree, remap_var_indices,
};
pub use crate::pass_contract::{
    DecompositionMeta, DiagField, OutcomeKind, PassOutcome, PendingWork, ReasonCategory,
    ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult, VerificationState,
};
pub use crate::result::{err, CobraError, ErrorInfo, Result};
pub use crate::signature_eval::{
    evaluate_boolean_signature, evaluate_boolean_signature_from_evaluator,
};
pub use crate::spot_check::{
    full_width_check_eval, verify_in_original_space, CheckResult, DEFAULT_NUM_SAMPLES,
};
pub use crate::simplify_outcome::{
    Diagnostic, Options, SimplifyOutcome, SimplifyOutcomeKind, SimplifyTelemetry,
};
