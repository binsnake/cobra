//! The `Options` bundle handed to the simplifier.

use cobra::core::classification::StructuralFlag;
use cobra::{is_valid_bitwidth, Options};
use pyo3::prelude::*;

use crate::errors::{invalid, Error};
use crate::flags;

/// Settings for one simplifier run.
///
/// Mirrors the Rust `Options` struct, minus its `evaluator` field, which is an
/// internal fast path the binding fills in itself.
#[pyclass(frozen, from_py_object, name = "Options", module = "cobra_mba")]
#[derive(Clone, Debug)]
pub struct PyOptions {
    pub(crate) bitwidth: u32,
    pub(crate) max_vars: u32,
    pub(crate) spot_check: bool,
    pub(crate) enable_bitwise_decomposition: bool,
    pub(crate) structural_flags: u32,
    pub(crate) require_lean_certificate: bool,
}

impl Default for PyOptions {
    fn default() -> Self {
        let d = Options::default();
        Self {
            bitwidth: d.bitwidth,
            max_vars: d.max_vars,
            spot_check: d.spot_check,
            enable_bitwise_decomposition: d.enable_bitwise_decomposition,
            structural_flags: d.structural_flags.0,
            require_lean_certificate: d.require_lean_certificate,
        }
    }
}

impl PyOptions {
    /// Convert to the library's own options struct.
    pub(crate) fn to_rust(&self) -> Options {
        Options {
            bitwidth: self.bitwidth,
            max_vars: self.max_vars,
            spot_check: self.spot_check,
            enable_bitwise_decomposition: self.enable_bitwise_decomposition,
            structural_flags: StructuralFlag(self.structural_flags),
            require_lean_certificate: self.require_lean_certificate,
            ..Options::default()
        }
    }

    pub(crate) fn checked(
        bitwidth: u32,
        max_vars: u32,
        spot_check: bool,
        enable_bitwise_decomposition: bool,
        structural_flags: u32,
        require_lean_certificate: bool,
    ) -> Result<Self, Error> {
        if !is_valid_bitwidth(bitwidth) {
            return Err(invalid(format!(
                "unsupported bitwidth {bitwidth} (must be in 1..=64)"
            )));
        }
        if max_vars == 0 {
            return Err(invalid("max_vars must be at least 1"));
        }
        Ok(Self {
            bitwidth,
            max_vars,
            spot_check,
            enable_bitwise_decomposition,
            structural_flags,
            require_lean_certificate,
        })
    }
}

#[pymethods]
impl PyOptions {
    #[new]
    #[pyo3(signature = (
        bitwidth = 64,
        max_vars = 16,
        spot_check = true,
        enable_bitwise_decomposition = true,
        structural_flags = 0,
        require_lean_certificate = true,
    ))]
    fn new(
        bitwidth: u32,
        max_vars: u32,
        spot_check: bool,
        enable_bitwise_decomposition: bool,
        structural_flags: u32,
        require_lean_certificate: bool,
    ) -> PyResult<Self> {
        Ok(Self::checked(
            bitwidth,
            max_vars,
            spot_check,
            enable_bitwise_decomposition,
            structural_flags,
            require_lean_certificate,
        )?)
    }

    /// Bit width the run works at, from 1 to 64.
    #[getter]
    fn bitwidth(&self) -> u32 {
        self.bitwidth
    }

    /// Largest variable count any subproblem may reach.
    #[getter]
    fn max_vars(&self) -> u32 {
        self.max_vars
    }

    /// Whether candidates are checked against sampled full-width probes.
    #[getter]
    fn spot_check(&self) -> bool {
        self.spot_check
    }

    /// Whether the bitwise decomposition passes may run.
    #[getter]
    fn enable_bitwise_decomposition(&self) -> bool {
        self.enable_bitwise_decomposition
    }

    /// Structural shapes to assume, on top of what the classifier finds.
    #[getter]
    fn structural_flags(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        flags::to_python(py, self.structural_flags)
    }

    /// Discard any simplification without a replayable Lean certificate.
    ///
    /// On by default, and it is the soundness gate: full-width checking is
    /// finite probing, so a candidate can differ from the original at exactly
    /// one point no probe reaches. Turning it off raises the simplification
    /// rate a great deal and is reasonable for non-adversarial input.
    #[getter]
    fn require_lean_certificate(&self) -> bool {
        self.require_lean_certificate
    }

    fn __repr__(&self) -> String {
        format!(
            "Options(bitwidth={}, max_vars={}, spot_check={}, \
             enable_bitwise_decomposition={}, structural_flags={}, \
             require_lean_certificate={})",
            self.bitwidth,
            self.max_vars,
            py_bool(self.spot_check),
            py_bool(self.enable_bitwise_decomposition),
            self.structural_flags,
            py_bool(self.require_lean_certificate),
        )
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.extract::<PyRef<'_, Self>>() {
            Ok(o) => {
                self.bitwidth == o.bitwidth
                    && self.max_vars == o.max_vars
                    && self.spot_check == o.spot_check
                    && self.enable_bitwise_decomposition == o.enable_bitwise_decomposition
                    && self.structural_flags == o.structural_flags
                    && self.require_lean_certificate == o.require_lean_certificate
            }
            Err(_) => false,
        }
    }
}

fn py_bool(b: bool) -> &'static str {
    if b {
        "True"
    } else {
        "False"
    }
}
