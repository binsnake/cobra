//! Exception types.
//!
//! Every `cobra::CobraError` variant gets its own Python class. The three
//! variants that mean "the caller passed something wrong" also inherit
//! `ValueError`, so ordinary Python error handling catches them. That is why
//! the classes are built with `type()` rather than PyO3's `create_exception!`
//! macro: the macro supports only a single base class.

use cobra::{CobraError, ErrorInfo};
use pyo3::exceptions::{PyException, PyValueError};
use pyo3::prelude::*;
use pyo3::sync::PyOnceLock;
use pyo3::types::{PyDict, PyTuple, PyType};

use crate::enums::PyErrorCode;

/// The exception classes, created once per interpreter.
pub struct Exceptions {
    pub base: Py<PyType>,
    pub invalid_argument: Py<PyType>,
    pub parse: Py<PyType>,
    pub non_linear: Py<PyType>,
    pub too_many_variables: Py<PyType>,
    pub no_reduction: Py<PyType>,
    pub verification_failed: Py<PyType>,
    pub simplification: Py<PyType>,
}

static EXCEPTIONS: PyOnceLock<Exceptions> = PyOnceLock::new();

fn new_exception(
    py: Python<'_>,
    name: &str,
    bases: &[&Bound<'_, PyType>],
    doc: &str,
) -> PyResult<Py<PyType>> {
    let namespace = PyDict::new(py);
    namespace.set_item("__module__", "cobra_mba")?;
    namespace.set_item("__doc__", doc)?;
    // Class-level defaults so the attributes exist even on an instance a
    // caller constructed directly.
    namespace.set_item("code", py.None())?;
    namespace.set_item("message", "")?;

    let bases = PyTuple::new(py, bases.iter().map(|b| b.as_any()))?;
    let type_fn = py.import("builtins")?.getattr("type")?;
    let class = type_fn.call1((name, bases, namespace))?;
    Ok(class.cast_into::<PyType>()?.unbind())
}

fn build(py: Python<'_>) -> PyResult<Exceptions> {
    let exception = py.get_type::<PyException>();
    let value_error = py.get_type::<PyValueError>();

    let base = new_exception(
        py,
        "CobraError",
        &[&exception],
        "Base class for every error raised by the CoBRA simplifier.\n\n\
         Carries `code` (an `ErrorCode`) and `message` (the text from the \
         Rust library).",
    )?;
    let base_bound = base.bind(py).clone();

    // Bad input is a ValueError as far as Python is concerned.
    let with_value_error: [&Bound<'_, PyType>; 2] = [&base_bound, &value_error];

    Ok(Exceptions {
        invalid_argument: new_exception(
            py,
            "InvalidArgumentError",
            &with_value_error,
            "An argument was outside the range the simplifier accepts.",
        )?,
        parse: new_exception(
            py,
            "ParseError",
            &with_value_error,
            "An expression string could not be parsed.",
        )?,
        too_many_variables: new_exception(
            py,
            "TooManyVariablesError",
            &with_value_error,
            "The expression has more variables than the simplifier allows.",
        )?,
        non_linear: new_exception(
            py,
            "NonLinearInputError",
            &[&base_bound],
            "The input is non-linear in a way this pass cannot handle.",
        )?,
        no_reduction: new_exception(
            py,
            "NoReductionError",
            &[&base_bound],
            "The simplifier found nothing to reduce.",
        )?,
        verification_failed: new_exception(
            py,
            "VerificationFailedError",
            &[&base_bound],
            "A candidate simplification failed its equivalence check.",
        )?,
        simplification: new_exception(
            py,
            "SimplificationError",
            &[&base_bound],
            "The pipeline returned an error outcome. Raised by \
             SimplifyResult.raise_for_error().",
        )?,
        base,
    })
}

pub fn exceptions(py: Python<'_>) -> PyResult<&'static Exceptions> {
    EXCEPTIONS.get_or_try_init(py, || build(py))
}

/// Register the exception classes on the extension module.
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    let e = exceptions(py)?;
    m.add("CobraError", e.base.bind(py))?;
    m.add("InvalidArgumentError", e.invalid_argument.bind(py))?;
    m.add("ParseError", e.parse.bind(py))?;
    m.add("NonLinearInputError", e.non_linear.bind(py))?;
    m.add("TooManyVariablesError", e.too_many_variables.bind(py))?;
    m.add("NoReductionError", e.no_reduction.bind(py))?;
    m.add("VerificationFailedError", e.verification_failed.bind(py))?;
    m.add("SimplificationError", e.simplification.bind(py))?;
    Ok(())
}

fn class_for(e: &Exceptions, code: CobraError) -> &Py<PyType> {
    match code {
        CobraError::InvalidArgument => &e.invalid_argument,
        CobraError::ParseError => &e.parse,
        CobraError::NonLinearInput => &e.non_linear,
        CobraError::TooManyVariables => &e.too_many_variables,
        CobraError::NoReduction => &e.no_reduction,
        CobraError::VerificationFailed => &e.verification_failed,
    }
}

/// Build a Python exception carrying `code` and `message`.
pub fn to_pyerr(py: Python<'_>, code: CobraError, message: &str) -> PyErr {
    let build = || -> PyResult<PyErr> {
        let e = exceptions(py)?;
        let class = class_for(e, code).bind(py);
        let instance = class.call1((message,))?;
        instance.setattr("code", PyErrorCode::from(code))?;
        instance.setattr("message", message)?;
        Ok(PyErr::from_value(instance))
    };
    build().unwrap_or_else(|e| e)
}

/// Raise `SimplificationError` for an error outcome.
pub fn simplification_error(py: Python<'_>, message: &str) -> PyErr {
    let build = || -> PyResult<PyErr> {
        let e = exceptions(py)?;
        let instance = e.simplification.bind(py).call1((message,))?;
        instance.setattr("code", py.None())?;
        instance.setattr("message", message)?;
        Ok(PyErr::from_value(instance))
    };
    build().unwrap_or_else(|e| e)
}

/// Wrapper that lets `?` turn a library error into the right Python exception.
pub struct Error(pub ErrorInfo);

impl From<ErrorInfo> for Error {
    fn from(info: ErrorInfo) -> Self {
        Self(info)
    }
}

impl From<Error> for PyErr {
    fn from(e: Error) -> Self {
        Python::attach(|py| to_pyerr(py, e.0.code, &e.0.message))
    }
}

/// Result type for helpers that fail the way the Rust library fails.
pub type Result<T> = std::result::Result<T, Error>;

/// Build an `InvalidArgument` failure from the binding's own validation.
pub fn invalid(message: impl Into<String>) -> Error {
    Error(ErrorInfo::new(CobraError::InvalidArgument, message))
}
