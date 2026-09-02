//! The `StructuralFlags` bitset.
//!
//! Built as a real `enum.IntFlag` so callers get Python's own flag behaviour:
//! `|`, `&`, `in`, and a readable repr. Constructing it here rather than in
//! `cobra_mba/__init__.py` keeps the native module self-contained, so the
//! getters below never have to import the package that imports them.

use cobra::core::classification::StructuralFlag;
use pyo3::prelude::*;
use pyo3::sync::PyOnceLock;
use pyo3::types::{PyList, PyType};

/// Name and bit of every flag the classifier sets, in bit order.
const FLAGS: &[(&str, u32)] = &[
    ("HAS_BITWISE", StructuralFlag::HAS_BITWISE.0),
    ("HAS_ARITHMETIC", StructuralFlag::HAS_ARITHMETIC.0),
    ("HAS_MUL", StructuralFlag::HAS_MUL.0),
    (
        "HAS_MULTILINEAR_PRODUCT",
        StructuralFlag::HAS_MULTILINEAR_PRODUCT.0,
    ),
    ("HAS_SINGLETON_POWER", StructuralFlag::HAS_SINGLETON_POWER.0),
    (
        "HAS_SINGLETON_POWER_GT2",
        StructuralFlag::HAS_SINGLETON_POWER_GT2.0,
    ),
    ("HAS_MIXED_PRODUCT", StructuralFlag::HAS_MIXED_PRODUCT.0),
    (
        "HAS_BITWISE_OVER_ARITH",
        StructuralFlag::HAS_BITWISE_OVER_ARITH.0,
    ),
    (
        "HAS_ARITH_OVER_BITWISE",
        StructuralFlag::HAS_ARITH_OVER_BITWISE.0,
    ),
    (
        "HAS_MULTIVAR_HIGH_POWER",
        StructuralFlag::HAS_MULTIVAR_HIGH_POWER.0,
    ),
    ("HAS_UNKNOWN_SHAPE", StructuralFlag::HAS_UNKNOWN_SHAPE.0),
];

static STRUCTURAL_FLAGS: PyOnceLock<Py<PyType>> = PyOnceLock::new();

fn build(py: Python<'_>) -> PyResult<Py<PyType>> {
    let members = PyList::empty(py);
    for (name, bit) in FLAGS {
        members.append((*name, *bit))?;
    }
    let int_flag = py.import("enum")?.getattr("IntFlag")?;
    let kwargs = pyo3::types::PyDict::new(py);
    kwargs.set_item("module", "cobra_mba")?;
    kwargs.set_item("qualname", "StructuralFlags")?;
    let class = int_flag.call(("StructuralFlags", members), Some(&kwargs))?;

    let class = class.cast_into::<PyType>()?;
    class.setattr(
        "__doc__",
        "Structural shapes the classifier found in an expression.",
    )?;
    // `UNSUPPORTED_MASK` is a composite of three flags rather than a bit of
    // its own, so it is attached after the members are defined.
    class.setattr("UNSUPPORTED_MASK", StructuralFlag::UNSUPPORTED_MASK.0)?;
    Ok(class.unbind())
}

/// The `StructuralFlags` class, created once per interpreter.
pub fn structural_flags_type(py: Python<'_>) -> PyResult<&'static Py<PyType>> {
    STRUCTURAL_FLAGS.get_or_try_init(py, || build(py))
}

/// Wrap a raw bitset in the `StructuralFlags` class.
pub fn to_python(py: Python<'_>, bits: u32) -> PyResult<Py<PyAny>> {
    let class = structural_flags_type(py)?;
    Ok(class.bind(py).call1((bits,))?.unbind())
}

/// Register the flag class on the extension module.
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    m.add("StructuralFlags", structural_flags_type(py)?.bind(py))?;
    Ok(())
}
