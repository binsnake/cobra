//! No-op tracing hooks matching upstream `Trace.h`'s default behavior.
//!
//! The C++ macros print only when `COBRA_ENABLE_TRACE` is defined. Rust keeps
//! the same zero-cost default surface with macros that type-check call sites
//! without evaluating trace formatting.

#[macro_export]
macro_rules! cobra_trace {
    ($component:expr, $($arg:tt)*) => {
        let _ = &$component;
    };
}

#[macro_export]
macro_rules! cobra_trace_expr {
    ($component:expr, $label:expr, $expr:expr, $vars:expr, $bitwidth:expr) => {
        let _ = (&$component, &$label, &$expr, &$vars, &$bitwidth);
    };
}

#[macro_export]
macro_rules! cobra_trace_sig {
    ($component:expr, $label:expr, $sig:expr) => {
        let _ = (&$component, &$label, &$sig);
    };
}

#[cfg(test)]
mod tests {
    use crate::Expr;

    #[test]
    fn trace_macros_compile_as_noops() {
        let expr = Expr::variable(0);
        let vars = vec!["x".to_string()];
        let sig = vec![0_u64, 1];
        crate::cobra_trace!("Core", "x={}", 1);
        crate::cobra_trace_expr!("Core", "expr", expr, vars, 64);
        crate::cobra_trace_sig!("Core", "sig", sig);
    }
}
