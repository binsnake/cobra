//! Python bindings for the CoBRA mixed Boolean-arithmetic simplifier.
//!
//! This crate is the only place PyO3's generated code lives; the library
//! crates it wraps keep `#![forbid(unsafe_code)]`. The Python-visible surface
//! is assembled in `cobra_mba/__init__.py`, which re-exports everything below
//! and adds the one-shot `simplify()` helper.

mod batch;
mod enums;
mod errors;
mod expr;
mod flags;
mod options;
mod outcome;
mod worker;

use cobra::{MAX_INPUT_VARS, MAX_VARIABLES};
use pyo3::prelude::*;
use pyo3::types::PyDict;

use crate::errors::Error;
use crate::options::PyOptions;
use crate::outcome::PySimplifyResult;
use crate::worker::run_detached;

/// Run the simplifier from a Boolean signature, with no expression tree.
///
/// Full-width verification is unavailable on this path, so results carry
/// weaker evidence than the expression entry point produces.
#[pyfunction]
#[pyo3(signature = (signature, variables, options = None))]
fn simplify_signature(
    py: Python<'_>,
    signature: Vec<u64>,
    variables: Vec<String>,
    options: Option<&PyOptions>,
) -> PyResult<PySimplifyResult> {
    let opts = options.cloned().unwrap_or_default();
    let rust_opts = opts.to_rust();
    let bitwidth = opts.bitwidth;
    let vars = variables.clone();
    let outcome = run_detached(py, move || {
        cobra::simplify(&signature, &vars, None, rust_opts)
    })?
    .map_err(Error)?;
    crate::outcome::build_signature_result(py, &outcome, &variables, bitwidth)
}

/// Version and build configuration of the native extension.
#[pyfunction]
fn build_info(py: Python<'_>) -> PyResult<Py<PyDict>> {
    let info = PyDict::new(py);
    info.set_item("version", env!("CARGO_PKG_VERSION"))?;
    let mut features: Vec<&str> = Vec::new();
    if cfg!(feature = "simd") {
        features.push("simd");
    }
    if cfg!(feature = "z3") {
        features.push("z3");
    }
    info.set_item("features", features)?;
    Ok(info.unbind())
}

#[pymodule]
fn _native(m: &Bound<'_, PyModule>) -> PyResult<()> {
    enums::register(m)?;
    flags::register(m)?;
    errors::register(m)?;
    expr::register(m)?;
    outcome::register(m)?;
    m.add_class::<PyOptions>()?;
    m.add_function(wrap_pyfunction!(simplify_signature, m)?)?;
    m.add_function(wrap_pyfunction!(batch::simplify_many, m)?)?;
    m.add_function(wrap_pyfunction!(build_info, m)?)?;

    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    m.add("MAX_BITWIDTH", 64u32)?;
    m.add("MAX_VARIABLES", MAX_VARIABLES)?;
    m.add("MAX_INPUT_VARS", MAX_INPUT_VARS)?;
    m.add("DEFAULT_MAX_VARS", 16u32)?;
    Ok(())
}
