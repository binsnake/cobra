//! No-op profiling hooks matching upstream `Profile.h`'s default behavior.
//!
//! Upstream expands these macros to Tracy calls only when profiling is
//! enabled; otherwise they compile to nothing. The Rust port exposes the
//! same call sites as no-op macros so downstream code can be instrumented
//! without taking a dependency on a profiler.

#[macro_export]
macro_rules! cobra_zone {
    () => {};
}

#[macro_export]
macro_rules! cobra_zone_n {
    ($name:expr) => {
        let _ = &$name;
    };
}

#[macro_export]
macro_rules! cobra_zone_text {
    ($text:expr) => {
        let _ = &$text;
    };
}

#[macro_export]
macro_rules! cobra_zone_value {
    ($value:expr) => {
        let _ = &$value;
    };
}

#[macro_export]
macro_rules! cobra_frame {
    () => {};
}

#[macro_export]
macro_rules! cobra_plot {
    ($name:expr, $value:expr) => {
        let _ = (&$name, &$value);
    };
}

#[macro_export]
macro_rules! cobra_msg {
    ($literal:expr) => {
        let _ = &$literal;
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn profiling_macros_compile_as_noops() {
        crate::cobra_zone!();
        crate::cobra_zone_n!("pass");
        crate::cobra_zone_text!("detail");
        crate::cobra_zone_value!(42);
        crate::cobra_frame!();
        crate::cobra_plot!("items", 7);
        crate::cobra_msg!("done");
    }
}
