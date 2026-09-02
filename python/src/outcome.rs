//! What one simplifier run produced: the expression, the evidence behind it,
//! and the diagnostics explaining anything that did not fire.

use std::sync::Arc;

use cobra::core::pass_contract::ReasonFrame;
use cobra::core::width::checked_width_of;
use cobra::{render, SimplifyOutcome};
use pyo3::prelude::*;
use pyo3::types::PyTuple;

use crate::enums::{
    PyOutcomeKind, PyProofLevel, PyReasonCategory, PyReasonDomain, PySemanticClass,
};
use crate::errors::{simplification_error, Error};
use crate::expr::PyExpr;
use crate::flags;

/// Per-run counters from the orchestrator.
#[pyclass(frozen, from_py_object, name = "Telemetry", module = "cobra_mba")]
#[derive(Clone, Copy, Debug)]
pub struct PyTelemetry {
    #[pyo3(get)]
    total_expansions: u32,
    #[pyo3(get)]
    max_depth_reached: u32,
    #[pyo3(get)]
    candidates_verified: u32,
    #[pyo3(get)]
    queue_high_water: u32,
}

#[pymethods]
impl PyTelemetry {
    fn __repr__(&self) -> String {
        format!(
            "Telemetry(total_expansions={}, max_depth_reached={}, \
             candidates_verified={}, queue_high_water={})",
            self.total_expansions,
            self.max_depth_reached,
            self.candidates_verified,
            self.queue_high_water
        )
    }
}

/// The identifier on a reason frame.
#[pyclass(frozen, from_py_object, name = "ReasonCode", module = "cobra_mba")]
#[derive(Clone, Copy, Debug)]
pub struct PyReasonCode {
    #[pyo3(get)]
    category: PyReasonCategory,
    #[pyo3(get)]
    domain: PyReasonDomain,
    #[pyo3(get)]
    subcode: u16,
}

#[pymethods]
impl PyReasonCode {
    fn __repr__(&self) -> String {
        format!(
            "ReasonCode(category={:?}, domain={:?}, subcode={})",
            self.category, self.domain, self.subcode
        )
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.extract::<PyRef<'_, Self>>() {
            Ok(o) => {
                self.category == o.category && self.domain == o.domain && self.subcode == o.subcode
            }
            Err(_) => false,
        }
    }
}

/// One level of the cause chain behind a diagnostic.
#[pyclass(frozen, from_py_object, name = "ReasonFrame", module = "cobra_mba")]
#[derive(Clone, Debug)]
pub struct PyReasonFrame {
    #[pyo3(get)]
    code: PyReasonCode,
    #[pyo3(get)]
    message: String,
    fields: Vec<(String, String)>,
}

#[pymethods]
impl PyReasonFrame {
    /// Key and value pairs attached to this frame, in the order recorded.
    ///
    /// A tuple rather than a dict, because nothing stops the same key
    /// appearing twice.
    #[getter]
    fn fields<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        PyTuple::new(py, self.fields.iter().map(|(k, v)| (k.clone(), v.clone())))
    }

    fn __repr__(&self) -> String {
        format!(
            "ReasonFrame(message={:?}, fields={})",
            self.message,
            self.fields.len()
        )
    }
}

impl PyReasonFrame {
    fn from_frame(frame: &ReasonFrame) -> Self {
        Self {
            code: PyReasonCode {
                category: frame.code.category.into(),
                domain: frame.code.domain.into(),
                subcode: frame.code.subcode,
            },
            message: frame.message.clone(),
            fields: frame
                .fields
                .iter()
                .map(|f| (f.key.clone(), f.value.clone()))
                .collect(),
        }
    }
}

/// Why the pipeline did what it did.
#[pyclass(frozen, from_py_object, name = "Diagnostic", module = "cobra_mba")]
#[derive(Clone, Debug)]
pub struct PyDiagnostic {
    #[pyo3(get)]
    semantic_class: PySemanticClass,
    structural_flags: u32,
    #[pyo3(get)]
    structural_transform_rounds: u32,
    #[pyo3(get)]
    transform_produced_candidate: bool,
    #[pyo3(get)]
    candidate_failed_verification: bool,
    #[pyo3(get)]
    reason: String,
    #[pyo3(get)]
    reason_code: Option<PyReasonCode>,
    cause_chain: Vec<PyReasonFrame>,
}

#[pymethods]
impl PyDiagnostic {
    /// Structural shapes the classifier found.
    #[getter]
    fn structural_flags(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        flags::to_python(py, self.structural_flags)
    }

    /// The frames explaining the top-level reason, outermost first.
    #[getter]
    fn cause_chain<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        PyTuple::new(py, self.cause_chain.iter().cloned())
    }

    fn __repr__(&self) -> String {
        format!(
            "Diagnostic(semantic_class={:?}, reason={:?}, causes={})",
            self.semantic_class,
            self.reason,
            self.cause_chain.len()
        )
    }
}

/// The result of one call to the simplifier.
#[pyclass(frozen, name = "SimplifyResult", module = "cobra_mba")]
pub struct PySimplifyResult {
    #[pyo3(get)]
    kind: PyOutcomeKind,
    #[pyo3(get)]
    expr: Option<Py<PyExpr>>,
    #[pyo3(get)]
    original: Py<PyExpr>,
    variables: Vec<String>,
    signature: Vec<u64>,
    #[pyo3(get)]
    verified: bool,
    #[pyo3(get)]
    proof_level: PyProofLevel,
    #[pyo3(get)]
    diagnostic: PyDiagnostic,
    #[pyo3(get)]
    telemetry: PyTelemetry,
}

#[pymethods]
impl PySimplifyResult {
    /// True when the pipeline returned a simplified expression.
    #[getter]
    fn simplified(&self) -> bool {
        self.kind == PyOutcomeKind::Simplified
    }

    /// Variables the result actually depends on, or the input's variables
    /// when the pipeline did not narrow them.
    #[getter]
    fn variables(&self) -> Vec<String> {
        self.variables.clone()
    }

    /// The Boolean signature the pipeline computed.
    #[getter]
    fn signature(&self) -> Vec<u64> {
        self.signature.clone()
    }

    /// Raise `SimplificationError` if the pipeline returned an error outcome.
    ///
    /// An error outcome is returned rather than raised so its diagnostic can
    /// be inspected; call this when an exception is the more convenient shape.
    fn raise_for_error(&self, py: Python<'_>) -> PyResult<()> {
        if self.kind == PyOutcomeKind::Error {
            let reason = if self.diagnostic.reason.is_empty() {
                "the simplifier returned an unspecified error"
            } else {
                &self.diagnostic.reason
            };
            return Err(simplification_error(py, reason));
        }
        Ok(())
    }

    /// The simplified expression when there is one, else the input, rendered
    /// the way `cobra-cli` prints it.
    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        let target = match (&self.expr, self.kind) {
            (Some(e), PyOutcomeKind::Simplified) => e.bind(py).get(),
            _ => self.original.bind(py).get(),
        };
        let expr = target.expr.clone();
        let vars = target.vars.clone();
        let bitwidth = target.bitwidth;
        crate::worker::run_detached(py, move || render(&expr, &vars, bitwidth))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let rendered = self.__str__(py)?;
        Ok(format!(
            "SimplifyResult(kind={:?}, proof_level={:?}, expr={rendered:?})",
            self.kind, self.proof_level
        ))
    }
}

/// Build the Python result from a finished run.
///
/// `original` is the expression that was handed to the pipeline; its variable
/// table is the namespace the simplified expression is mapped back into.
pub fn build_result(
    py: Python<'_>,
    outcome: &SimplifyOutcome,
    original: &Bound<'_, PyExpr>,
) -> PyResult<PySimplifyResult> {
    let input = original.get();

    // Same remapping the CLI does before rendering: a result that dropped
    // variables is indexed against `real_vars`, not the caller's table.
    let simplified = cobra::outcome_expr_in_original_space(outcome, &input.vars);
    let expr = match simplified {
        Some(tree) => {
            let width = checked_width_of(&tree, &input.widths, input.bitwidth).map_err(Error)?;
            let handle = PyExpr::new(
                tree,
                input.vars.clone(),
                input.widths.clone(),
                input.bitwidth,
                width,
            );
            Some(Py::new(py, handle)?)
        }
        None => None,
    };

    let variables = if outcome.real_vars.is_empty() {
        input.vars.as_ref().clone()
    } else {
        outcome.real_vars.clone()
    };

    let diag = &outcome.diag;
    let diagnostic = PyDiagnostic {
        semantic_class: diag.classification.semantic.into(),
        structural_flags: diag.classification.flags.0,
        structural_transform_rounds: diag.structural_transform_rounds,
        transform_produced_candidate: diag.transform_produced_candidate,
        candidate_failed_verification: diag.candidate_failed_verification,
        reason: diag.reason.clone(),
        reason_code: diag.reason_code.map(|c| PyReasonCode {
            category: c.category.into(),
            domain: c.domain.into(),
            subcode: c.subcode,
        }),
        cause_chain: diag
            .cause_chain
            .iter()
            .map(PyReasonFrame::from_frame)
            .collect(),
    };

    let telemetry = PyTelemetry {
        total_expansions: outcome.telemetry.total_expansions,
        max_depth_reached: outcome.telemetry.max_depth_reached,
        candidates_verified: outcome.telemetry.candidates_verified,
        queue_high_water: outcome.telemetry.queue_high_water,
    };

    Ok(PySimplifyResult {
        kind: outcome.kind.into(),
        expr,
        original: original.clone().unbind(),
        variables,
        signature: outcome.sig_vector.clone(),
        verified: outcome.verified,
        proof_level: outcome.proof_level.into(),
        diagnostic,
        telemetry,
    })
}

/// Build a result for the signature-only entry point, which has no input tree.
pub fn build_signature_result(
    py: Python<'_>,
    outcome: &SimplifyOutcome,
    vars: &[String],
    bitwidth: u32,
) -> PyResult<PySimplifyResult> {
    // The signature path has no original expression, so a constant zero of the
    // right shape stands in as the input.
    let placeholder = PyExpr::new(
        cobra::Expr::constant(0),
        Arc::new(vars.to_vec()),
        Arc::new(vec![bitwidth; vars.len()]),
        bitwidth,
        bitwidth,
    );
    let bound = Bound::new(py, placeholder)?;
    build_result(py, outcome, &bound)
}

/// Register the outcome types on the extension module.
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySimplifyResult>()?;
    m.add_class::<PyDiagnostic>()?;
    m.add_class::<PyReasonCode>()?;
    m.add_class::<PyReasonFrame>()?;
    m.add_class::<PyTelemetry>()?;
    Ok(())
}
