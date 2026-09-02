//! Runs simplifier work off the Python thread.
//!
//! Two problems are solved together. Python holds the global interpreter lock
//! while a native call runs, so a long simplification would block every other
//! thread; and CPython's own threads get a small stack (1 MiB on Windows),
//! while the pipeline recurses deeply enough that `cobra-cli` gives its worker
//! 64 MiB. Every entry point that reaches the pipeline goes through
//! [`run_detached`], which releases the lock and runs the closure on a thread
//! with the same stack size the CLI uses.

use std::any::Any;

use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;

/// Matches `CLI_STACK_SIZE` in `crates/cobra-cli/src/main.rs`.
pub const WORKER_STACK: usize = 64 * 1024 * 1024;

/// A thread configured the way every CoBRA worker is configured.
pub fn worker_builder() -> std::thread::Builder {
    std::thread::Builder::new()
        .name("cobra-mba".into())
        .stack_size(WORKER_STACK)
}

/// Release the GIL and run `f` on a worker thread with a large stack.
pub fn run_detached<T, F>(py: Python<'_>, f: F) -> PyResult<T>
where
    T: Send,
    F: FnOnce() -> T + Send,
{
    py.detach(move || {
        std::thread::scope(|scope| {
            let handle = worker_builder().spawn_scoped(scope, f).map_err(|e| {
                PyRuntimeError::new_err(format!("could not start the CoBRA worker thread: {e}"))
            })?;
            handle
                .join()
                .map_err(|payload| PyRuntimeError::new_err(panic_message(payload.as_ref())))
        })
    })
}

/// Recover a readable message from a panic payload.
fn panic_message(payload: &(dyn Any + Send)) -> String {
    let detail = if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "no panic message".to_string()
    };
    format!("the CoBRA simplifier panicked: {detail}")
}
