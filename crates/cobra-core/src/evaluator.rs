//! Type-erased callable for evaluating an expression.
//!
//! `shared_ptr<const CompiledExpr>` (fast path) or a `std::function` (fallback
//! for arbitrary callables and for the variable-remapping case that the
//! compiled path can't cover directly).
//!
//! `Arc<dyn Fn(&[u64]) -> u64 + Send + Sync>` arms. Clones are cheap.

use std::sync::Arc;

use crate::compiled::{compile, eval, CompiledExpr};
use crate::expr::Expr;

/// actual tracing integration is added in `cobra-analysis` / the `tracing`
/// feature of downstream crates.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum TraceKind {
    #[default]
    None,
    Root,
    MappedGlobal,
    MappedOverride,
    Remainder,
    LiftedOuter,
    CliOriginalAst,
}

/// Scratch buffers shared across evaluations to avoid re-allocating.
/// `remapped_inputs` is used when the evaluator has an `input_map`;
/// `stack` is used by the compiled path.
#[derive(Clone, Debug, Default)]
pub struct Workspace {
    pub remapped_inputs: Vec<u64>,
    pub stack: Vec<u64>,
}

type Closure = dyn Fn(&[u64]) -> u64 + Send + Sync + 'static;

#[derive(Clone)]
enum EvalBody {
    Compiled(Arc<CompiledExpr>),
    Closure(Arc<Closure>),
}

#[derive(Clone, Default)]
pub struct Evaluator {
    body: Option<EvalBody>,
    /// When set, the caller's vector is treated as the reduced-arity input;
    /// entry `i` writes to `input_map[i]` in a wider buffer before invoking
    input_map: Vec<u32>,
    input_arity: u32,
    trace_kind: TraceKind,
}

impl std::fmt::Debug for Evaluator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Evaluator")
            .field(
                "body",
                &match &self.body {
                    None => "None",
                    Some(EvalBody::Compiled(_)) => "Compiled",
                    Some(EvalBody::Closure(_)) => "Closure",
                },
            )
            .field("input_map", &self.input_map)
            .field("input_arity", &self.input_arity)
            .field("trace_kind", &self.trace_kind)
            .finish()
    }
}

impl Evaluator {
    #[must_use]
    pub fn from_closure<F>(f: F) -> Self
    where
        F: Fn(&[u64]) -> u64 + Send + Sync + 'static,
    {
        Self {
            body: Some(EvalBody::Closure(Arc::new(f))),
            input_map: Vec::new(),
            input_arity: 0,
            trace_kind: TraceKind::None,
        }
    }

    #[must_use]
    pub fn from_expr(expr: &Expr, bitwidth: u32) -> Self {
        Self::from_compiled(Arc::new(compile(expr, bitwidth)), TraceKind::None)
    }

    #[must_use]
    pub fn from_compiled(compiled: Arc<CompiledExpr>, trace_kind: TraceKind) -> Self {
        let arity = compiled.arity;
        Self {
            body: Some(EvalBody::Compiled(compiled)),
            input_map: Vec::new(),
            input_arity: arity,
            trace_kind,
        }
    }

    #[must_use]
    pub fn with_trace(mut self, trace_kind: TraceKind) -> Self {
        self.trace_kind = trace_kind;
        self
    }

    #[must_use]
    pub fn has_body(&self) -> bool {
        self.body.is_some()
    }

    #[must_use]
    pub fn has_compiled(&self) -> bool {
        matches!(self.body, Some(EvalBody::Compiled(_)))
    }

    #[must_use]
    pub fn input_arity(&self) -> u32 {
        self.input_arity
    }

    #[must_use]
    pub fn required_stack_size(&self) -> usize {
        match &self.body {
            Some(EvalBody::Compiled(c)) => c.stack_size,
            _ => 0,
        }
    }

    #[must_use]
    pub fn trace_kind(&self) -> TraceKind {
        self.trace_kind
    }

    /// Evaluate with a fresh internal workspace. For repeated calls on the
    /// hot path, prefer [`Evaluator::eval_with`] and pass in a reusable one.
    #[must_use]
    pub fn eval(&self, vals: &[u64]) -> u64 {
        let mut ws = Workspace::default();
        self.eval_with(vals, &mut ws)
    }

    /// Evaluate using the provided scratch workspace.
    pub fn eval_with(&self, vals: &[u64], ws: &mut Workspace) -> u64 {
        let body = self.body.as_ref().expect("evaluator has no body");
        match body {
            EvalBody::Compiled(c) => self.eval_compiled(c, vals, ws),
            EvalBody::Closure(f) => {
                if self.input_map.is_empty() {
                    f(vals)
                } else {
                    // For the closure path we allocate a fresh remapped buffer
                    // each call. This path is cold (closures are used by
                    // externally-supplied evaluators that don't want the
                    // bytecode form); the compiled path is the fast one.
                    let remapped = self.remap_vals(vals);
                    f(&remapped)
                }
            }
        }
    }

    fn eval_compiled(&self, c: &CompiledExpr, vals: &[u64], ws: &mut Workspace) -> u64 {
        if self.input_map.is_empty() {
            return eval(c, vals, &mut ws.stack);
        }

        let mut remapped_arity = c.arity as usize;
        for &idx in &self.input_map {
            remapped_arity = remapped_arity.max(idx as usize + 1);
        }
        if ws.remapped_inputs.len() < remapped_arity {
            ws.remapped_inputs.resize(remapped_arity, 0);
        }
        ws.remapped_inputs
            .iter_mut()
            .take(remapped_arity)
            .for_each(|v| *v = 0);
        for (i, &dst) in self.input_map.iter().enumerate() {
            ws.remapped_inputs[dst as usize] = vals[i];
        }
        eval(c, &ws.remapped_inputs, &mut ws.stack)
    }

    fn remap_vals(&self, vals: &[u64]) -> Vec<u64> {
        // Buffer size covers every destination index referenced by the map.
        let mut buf_size: usize = 0;
        for &idx in &self.input_map {
            buf_size = buf_size.max(idx as usize + 1);
        }
        let mut out = vec![0u64; buf_size];
        for (i, &dst) in self.input_map.iter().enumerate() {
            out[dst as usize] = vals[i];
        }
        out
    }

    /// Produce a new evaluator that expects `idx_map.len()` inputs, each one
    /// feeding into the `idx_map[i]`'th slot of the underlying body. When the
    /// `Remap` behaviour); when it's a closure, the new evaluator wraps the
    /// old one in a remap shim.
    #[must_use]
    pub fn remap(&self, idx_map: &[u32], source_arity: u32, trace_kind: TraceKind) -> Evaluator {
        match &self.body {
            Some(EvalBody::Compiled(_)) => {
                let mut composed = Vec::with_capacity(idx_map.len());
                if self.input_map.is_empty() {
                    composed.extend_from_slice(idx_map);
                } else {
                    for &idx in idx_map {
                        composed.push(self.input_map[idx as usize]);
                    }
                }
                Evaluator {
                    body: self.body.clone(),
                    input_map: composed,
                    input_arity: u32::try_from(idx_map.len()).unwrap_or(u32::MAX),
                    trace_kind,
                }
            }
            Some(EvalBody::Closure(_)) | None => {
                // Match the C++ behaviour: wrap the current evaluator in a
                // closure that scatters reduced inputs into a wider buffer
                // sized for both `source_arity` and any destination in
                // `idx_map`.
                let base = self.clone();
                let idx_map = idx_map.to_vec();
                let mut buf_size = source_arity as usize;
                for &idx in &idx_map {
                    buf_size = buf_size.max(idx as usize + 1);
                }
                Evaluator::from_closure(move |reduced: &[u64]| {
                    let mut original_vals = vec![0u64; buf_size];
                    for (i, &dst) in idx_map.iter().enumerate() {
                        original_vals[dst as usize] = reduced[i];
                    }
                    base.eval(&original_vals)
                })
                .with_trace(trace_kind)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_has_no_body() {
        let e = Evaluator::default();
        assert!(!e.has_body());
        assert!(!e.has_compiled());
        assert_eq!(e.input_arity(), 0);
    }

    #[test]
    fn from_expr_evaluates() {
        let e = Evaluator::from_expr(&Expr::add(Expr::variable(0), Expr::variable(1)), 64);
        assert!(e.has_compiled());
        assert_eq!(e.eval(&[3, 4]), 7);
    }

    #[test]
    fn from_closure_evaluates() {
        let e = Evaluator::from_closure(|vals| vals[0].wrapping_mul(vals[1]));
        assert!(e.has_body());
        assert!(!e.has_compiled());
        assert_eq!(e.eval(&[6, 7]), 42);
    }

    #[test]
    fn workspace_reuses_stack() {
        let e = Evaluator::from_expr(&Expr::add(Expr::variable(0), Expr::variable(1)), 64);
        let mut ws = Workspace::default();
        for (a, b) in [(1u64, 2), (3, 5), (100, 200)] {
            assert_eq!(e.eval_with(&[a, b], &mut ws), a.wrapping_add(b));
        }
        assert!(!ws.stack.is_empty());
    }

    #[test]
    fn remap_compiled_swaps_inputs() {
        // Underlying evaluator computes x0 - x1 (via add+neg) so the result
        // is order-sensitive. `idx_map[i] = j` means "my input i goes to the
        // underlying's slot j", so remap with [1, 0] swaps the two inputs.
        let expr = Expr::add(Expr::variable(0), Expr::neg(Expr::variable(1)));
        let base = Evaluator::from_expr(&expr, 64);
        let swapped = base.remap(&[1, 0], 2, TraceKind::None);
        assert_eq!(swapped.input_arity(), 2);
        assert_eq!(base.eval(&[3, 4]), swapped.eval(&[4, 3]));
    }

    #[test]
    fn remap_closure_scatters_into_wider_buffer() {
        let base = Evaluator::from_closure(|vals: &[u64]| vals.iter().copied().sum());
        let remapped = base.remap(&[0, 2], 3, TraceKind::None);
        // remapped takes 2 inputs: slot0 -> pos 0, slot1 -> pos 2; pos 1 stays 0.
        assert_eq!(remapped.eval(&[5, 7]), 12);
    }
}
