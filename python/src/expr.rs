//! The `Expr` handle: an expression tree plus the variable table it is
//! indexed against.
//!
//! The library indexes variables by position and keeps their names in a
//! separate list, so an expression alone is not self-describing. `Expr` binds
//! the two together, which is what lets Python callers combine trees that were
//! built independently: the operators take the sorted union of both variable
//! tables and renumber each side into it.
//!
//! Every node caches its own result width. Widths are then checked in constant
//! time as each node is built, instead of re-walking the whole tree.

use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

use cobra::core::arith::bitmask;
use cobra::core::evaluator::{Evaluator, Workspace};
use cobra::core::expr_rewrite::build_var_support;
use cobra::core::expr_utils::{eval_constant, is_constant_subtree, remap_var_indices};
use cobra::core::signature_eval::try_evaluate_boolean_signature;
use cobra::core::width::{checked_width_of, validate_widths};
// The builder must accept exactly what the parser accepts, so the limit is
// taken from the parser rather than mirrored here.
use cobra::parser::postfix::MAX_EXPONENT;
use cobra::{is_valid_bitwidth, parse_to_ast, render, simplify_expr, Expr, Kind, MAX_VARIABLES};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::{PyByteArray, PyBytes, PyDict, PyInt, PyList, PySequence, PyString, PyTuple};

use crate::enums::PyKind;
use crate::errors::{invalid, Error, Result};
use crate::options::PyOptions;
use crate::outcome::PySimplifyResult;
use crate::worker::run_detached;

/// Deepest tree `to_dict` will walk. Python's own recursion limit is 1000, so
/// a deeper dictionary could not be consumed from Python anyway.
const MAX_DICT_DEPTH: u32 = 1024;

/// An expression tree together with its variable names and widths.
#[pyclass(frozen, name = "Expr", module = "cobra_mba")]
pub struct PyExpr {
    pub(crate) expr: Arc<Expr>,
    pub(crate) vars: Arc<Vec<String>>,
    pub(crate) widths: Arc<Vec<u32>>,
    /// Width constants take, and the width of any variable with no entry of
    /// its own. This is the "bitwidth" the CLI and the simplifier talk about.
    pub(crate) bitwidth: u32,
    /// Result width of this tree, which differs from `bitwidth` only when the
    /// tree contains casts or concatenations.
    pub(crate) width: u32,
    evaluator: OnceLock<Evaluator>,
}

impl PyExpr {
    pub(crate) fn new(
        expr: Arc<Expr>,
        vars: Arc<Vec<String>>,
        widths: Arc<Vec<u32>>,
        bitwidth: u32,
        width: u32,
    ) -> Self {
        Self {
            expr,
            vars,
            widths,
            bitwidth,
            width,
            evaluator: OnceLock::new(),
        }
    }

    /// Build from parts whose width relationships have not been checked yet.
    pub(crate) fn checked(
        expr: Arc<Expr>,
        vars: Vec<String>,
        widths: Vec<u32>,
        bitwidth: u32,
    ) -> Result<Self> {
        if !is_valid_bitwidth(bitwidth) {
            return Err(invalid(format!(
                "unsupported bitwidth {bitwidth} (must be in 1..=64)"
            )));
        }
        if vars.len() != widths.len() {
            return Err(invalid(format!(
                "variable table has {} names but {} widths",
                vars.len(),
                widths.len()
            )));
        }
        if vars.len() > MAX_VARIABLES {
            return Err(Error(cobra::ErrorInfo::new(
                cobra::CobraError::TooManyVariables,
                format!(
                    "{} variables exceeds the limit of {MAX_VARIABLES}",
                    vars.len()
                ),
            )));
        }
        validate_widths(&expr, &widths, bitwidth)?;
        let width = checked_width_of(&expr, &widths, bitwidth)?;
        Ok(Self::new(
            expr,
            Arc::new(vars),
            Arc::new(widths),
            bitwidth,
            width,
        ))
    }

    fn evaluator(&self) -> Result<&Evaluator> {
        if let Some(e) = self.evaluator.get() {
            return Ok(e);
        }
        let built = Evaluator::try_from_expr(&self.expr, self.bitwidth)?;
        Ok(self.evaluator.get_or_init(|| built))
    }

    fn same_table(&self, other: &PyExpr) -> bool {
        Arc::ptr_eq(&self.vars, &other.vars) || *self.vars == *other.vars
    }
}

/// Two operands renumbered into one shared variable table.
struct Aligned {
    left: Arc<Expr>,
    right: Arc<Expr>,
    vars: Arc<Vec<String>>,
    widths: Arc<Vec<u32>>,
    bitwidth: u32,
    left_width: u32,
    right_width: u32,
}

/// Collapse a constant-only tree to a single constant at `bitwidth`.
fn refold_constant(expr: &Expr, bitwidth: u32) -> Arc<Expr> {
    Expr::constant(eval_constant(expr, bitwidth))
}

fn is_bare_constant(e: &PyExpr) -> bool {
    e.vars.is_empty() && is_constant_subtree(&e.expr)
}

/// Put both operands in one variable table and one bitwidth.
fn align(a: &PyExpr, b: &PyExpr) -> Result<Aligned> {
    // A constant carries no variables and no width of its own worth keeping,
    // so it adopts the other side's bitwidth rather than forcing a mismatch.
    let (left, left_width, right, right_width, bitwidth) = if a.bitwidth == b.bitwidth {
        (a.expr.clone(), a.width, b.expr.clone(), b.width, a.bitwidth)
    } else if is_bare_constant(a) {
        let folded = refold_constant(&a.expr, b.bitwidth);
        (folded, b.bitwidth, b.expr.clone(), b.width, b.bitwidth)
    } else if is_bare_constant(b) {
        let folded = refold_constant(&b.expr, a.bitwidth);
        (a.expr.clone(), a.width, folded, a.bitwidth, a.bitwidth)
    } else {
        return Err(invalid(format!(
            "expressions have different bitwidths: {} and {}",
            a.bitwidth, b.bitwidth
        )));
    };

    // Fast path: identical tables need no renumbering.
    if a.same_table(b) {
        return Ok(Aligned {
            left,
            right,
            vars: a.vars.clone(),
            widths: a.widths.clone(),
            bitwidth,
            left_width,
            right_width,
        });
    }

    let (vars, widths) = union_tables(&a.vars, &a.widths, &b.vars, &b.widths)?;
    let left = renumber(left, &a.vars, &vars);
    let right = renumber(right, &b.vars, &vars);

    Ok(Aligned {
        left,
        right,
        vars: Arc::new(vars),
        widths: Arc::new(widths),
        bitwidth,
        left_width,
        right_width,
    })
}

/// Sorted union of two variable tables, rejecting a name used at two widths.
fn union_tables(
    a_vars: &[String],
    a_widths: &[u32],
    b_vars: &[String],
    b_widths: &[u32],
) -> Result<(Vec<String>, Vec<u32>)> {
    // A `BTreeMap` orders names exactly the way the parser's `BTreeSet` does,
    // so a built tree and a parsed one agree on variable order.
    let mut merged: BTreeMap<&str, u32> = BTreeMap::new();
    for (name, width) in a_vars.iter().zip(a_widths) {
        merged.insert(name.as_str(), *width);
    }
    for (name, width) in b_vars.iter().zip(b_widths) {
        if let Some(existing) = merged.get(name.as_str()) {
            if existing != width {
                return Err(invalid(format!(
                    "variable {name} is {existing} bits wide on one side and {width} on the other"
                )));
            }
        }
        merged.insert(name.as_str(), *width);
    }
    if merged.len() > MAX_VARIABLES {
        return Err(Error(cobra::ErrorInfo::new(
            cobra::CobraError::TooManyVariables,
            format!(
                "combining these expressions needs {} variables, over the limit of {MAX_VARIABLES}",
                merged.len()
            ),
        )));
    }
    let vars: Vec<String> = merged.keys().map(|s| (*s).to_string()).collect();
    let widths: Vec<u32> = merged.values().copied().collect();
    Ok((vars, widths))
}

/// Renumber `expr` from `from_vars` index space into `to_vars` index space.
fn renumber(expr: Arc<Expr>, from_vars: &[String], to_vars: &[String]) -> Arc<Expr> {
    if from_vars == to_vars || from_vars.is_empty() {
        return expr;
    }
    let index_map = build_var_support(to_vars, from_vars);
    let mut owned = expr;
    remap_var_indices(Arc::make_mut(&mut owned), &index_map);
    owned
}

/// The same-width binary operators, which all require equal operand widths.
enum SameWidth {
    Add,
    Mul,
    And,
    Or,
    Xor,
}

fn same_width_op(a: &PyExpr, b: &PyExpr, op: &SameWidth) -> Result<PyExpr> {
    let al = align(a, b)?;
    if al.left_width != al.right_width {
        return Err(invalid(format!(
            "width mismatch: operands are {} and {} bits wide",
            al.left_width, al.right_width
        )));
    }
    let expr = match op {
        SameWidth::Add => Expr::add(al.left, al.right),
        SameWidth::Mul => Expr::mul(al.left, al.right),
        SameWidth::And => Expr::and(al.left, al.right),
        SameWidth::Or => Expr::or(al.left, al.right),
        SameWidth::Xor => Expr::xor(al.left, al.right),
    };
    Ok(PyExpr::new(
        expr,
        al.vars,
        al.widths,
        al.bitwidth,
        al.left_width,
    ))
}

/// Turn a Python operand into an expression in `like`'s world.
///
/// Accepts another `Expr` or a plain integer; anything else yields `None` so
/// the caller can return `NotImplemented` and let Python try the reflected
/// operation.
fn coerce(other: &Bound<'_, PyAny>, like: &PyExpr) -> PyResult<Option<PyExpr>> {
    if let Ok(e) = other.extract::<PyRef<'_, PyExpr>>() {
        return Ok(Some(PyExpr::new(
            e.expr.clone(),
            e.vars.clone(),
            e.widths.clone(),
            e.bitwidth,
            e.width,
        )));
    }
    if other.is_instance_of::<PyInt>() {
        let value = extract_masked(other, like.bitwidth)?;
        return Ok(Some(PyExpr::new(
            Expr::constant(value),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            like.bitwidth,
            like.bitwidth,
        )));
    }
    Ok(None)
}

/// Read a Python integer and reduce it modulo `2 ** bitwidth`.
fn extract_masked(value: &Bound<'_, PyAny>, bitwidth: u32) -> PyResult<u64> {
    let raw = if let Ok(v) = value.extract::<u64>() {
        v
    } else if let Ok(v) = value.extract::<i64>() {
        v as u64
    } else {
        return Err(Error::from(cobra::ErrorInfo::new(
            cobra::CobraError::InvalidArgument,
            "integer does not fit in 64 bits",
        ))
        .into());
    };
    Ok(raw & bitmask(bitwidth))
}

fn not_implemented(py: Python<'_>) -> Py<PyAny> {
    py.NotImplemented()
}

#[pymethods]
impl PyExpr {
    /// Parse an expression written in the simplifier's infix syntax.
    ///
    /// Variables are collected and sorted lexicographically, so
    /// `Expr.parse("b + a").variables` is `["a", "b"]`.
    #[staticmethod]
    #[pyo3(signature = (text, bitwidth = 64))]
    fn parse(py: Python<'_>, text: &str, bitwidth: u32) -> PyResult<Self> {
        let owned = text.to_string();
        let parsed = run_detached(py, move || parse_to_ast(&owned, bitwidth))?.map_err(Error)?;
        Ok(Self::checked(
            parsed.expr,
            parsed.vars,
            parsed.var_widths,
            bitwidth,
        )?)
    }

    /// A single variable.
    #[staticmethod]
    #[pyo3(signature = (name, width = 64))]
    fn var(name: &str, width: u32) -> PyResult<Self> {
        check_identifier(name)?;
        if !is_valid_bitwidth(width) {
            return Err(invalid(format!("unsupported width {width} (must be in 1..=64)")).into());
        }
        Ok(Self::new(
            Expr::variable(0),
            Arc::new(vec![name.to_string()]),
            Arc::new(vec![width]),
            width,
            width,
        ))
    }

    /// A constant, reduced modulo `2 ** width`.
    #[staticmethod]
    #[pyo3(name = "const", signature = (value, width = 64))]
    fn const_(value: &Bound<'_, PyAny>, width: u32) -> PyResult<Self> {
        if !is_valid_bitwidth(width) {
            return Err(invalid(format!("unsupported width {width} (must be in 1..=64)")).into());
        }
        let masked = extract_masked(value, width)?;
        Ok(Self::new(
            Expr::constant(masked),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            width,
            width,
        ))
    }

    /// Bit concatenation: `high` supplies the top bits, `low` the bottom.
    #[staticmethod]
    fn concat(high: &Self, low: &Self) -> PyResult<Self> {
        let al = align(high, low)?;
        let width = al
            .left_width
            .checked_add(al.right_width)
            .filter(|w| (1..=64).contains(w))
            .ok_or_else(|| {
                invalid(format!(
                    "concatenating {}-bit and {}-bit values needs more than 64 bits",
                    al.left_width, al.right_width
                ))
            })?;
        Ok(Self::new(
            Expr::concat(al.left, al.right),
            al.vars,
            al.widths,
            al.bitwidth,
            width,
        ))
    }

    /// Rebuild an expression from `to_dict` output.
    #[staticmethod]
    fn from_dict(state: &Bound<'_, PyDict>) -> PyResult<Self> {
        let bitwidth: u32 = get_item(state, "bitwidth")?.extract()?;
        let vars: Vec<String> = get_item(state, "variables")?.extract()?;
        let widths: Vec<u32> = match state.get_item("variable_widths")? {
            Some(w) => w.extract()?,
            None => vec![bitwidth; vars.len()],
        };
        let node = get_item(state, "expr")?;
        let node = node.cast::<PyDict>().map_err(|_| {
            PyTypeError::new_err("the \"expr\" entry must be a dict describing a node")
        })?;
        let expr = node_from_dict(node, vars.len(), 0)?;
        Ok(Self::checked(expr, vars, widths, bitwidth)?)
    }

    /// Variable names, in the order the indices refer to.
    #[getter]
    fn variables(&self) -> Vec<String> {
        self.vars.as_ref().clone()
    }

    /// Per-variable bit widths, one entry per name in `variables`.
    #[getter]
    fn variable_widths(&self) -> Vec<u32> {
        self.widths.as_ref().clone()
    }

    /// Width constants take, and the width the simplifier runs at.
    #[getter]
    fn bitwidth(&self) -> u32 {
        self.bitwidth
    }

    /// Result width of this tree. Differs from `bitwidth` only under a cast
    /// or a concatenation.
    #[getter]
    fn width(&self) -> u32 {
        self.width
    }

    /// This node's kind.
    #[getter]
    fn kind(&self) -> PyKind {
        PyKind::from(&self.expr.kind)
    }

    /// The child expressions, each carrying the same variable table.
    #[getter]
    fn children(&self) -> Result<Vec<Self>> {
        self.expr
            .children
            .iter()
            .map(|child| {
                let width = checked_width_of(child, &self.widths, self.bitwidth)?;
                Ok(Self::new(
                    child.clone(),
                    self.vars.clone(),
                    self.widths.clone(),
                    self.bitwidth,
                    width,
                ))
            })
            .collect()
    }

    /// Value of a `CONSTANT` node, else `None`.
    #[getter]
    fn value(&self) -> Option<u64> {
        match self.expr.kind {
            Kind::Constant(v) => Some(v),
            _ => None,
        }
    }

    /// Index of a `VARIABLE` node into `variables`, else `None`.
    #[getter]
    fn variable_index(&self) -> Option<u32> {
        match self.expr.kind {
            Kind::Variable(i) => Some(i),
            _ => None,
        }
    }

    /// Name of a `VARIABLE` node, else `None`.
    #[getter]
    fn variable_name(&self) -> Option<String> {
        match self.expr.kind {
            Kind::Variable(i) => self.vars.get(i as usize).cloned(),
            _ => None,
        }
    }

    /// Shift amount of a `SHR` node, else `None`.
    #[getter]
    fn shift_amount(&self) -> Option<u32> {
        match self.expr.kind {
            Kind::Shr(k) => Some(k),
            _ => None,
        }
    }

    /// Target width of a `ZEXT`, `SEXT`, or `TRUNC` node, else `None`.
    #[getter]
    fn target_width(&self) -> Option<u32> {
        match self.expr.kind {
            Kind::ZExt(w) | Kind::SExt(w) | Kind::Trunc(w) => Some(w),
            _ => None,
        }
    }

    /// Render back to the infix syntax `parse` accepts.
    fn render(&self, py: Python<'_>) -> PyResult<String> {
        let expr = self.expr.clone();
        let vars = self.vars.clone();
        let bitwidth = self.bitwidth;
        run_detached(py, move || render(&expr, &vars, bitwidth))
    }

    /// Zero-extend to `width` bits.
    fn zext(&self, width: u32) -> Result<Self> {
        self.cast_to(width, Kind::ZExt(width))
    }

    /// Sign-extend to `width` bits.
    fn sext(&self, width: u32) -> Result<Self> {
        self.cast_to(width, Kind::SExt(width))
    }

    /// Truncate to the low `width` bits.
    fn trunc(&self, width: u32) -> Result<Self> {
        self.cast_to(width, Kind::Trunc(width))
    }

    /// Evaluate at concrete variable values.
    ///
    /// Values may be given as a mapping, as a sequence in variable order, or
    /// as keyword arguments. Each is reduced modulo its variable's width.
    #[pyo3(signature = (values = None, **kwargs))]
    fn evaluate(
        &self,
        values: Option<&Bound<'_, PyAny>>,
        kwargs: Option<&Bound<'_, PyDict>>,
    ) -> PyResult<u64> {
        let mut slots: Vec<Option<u64>> = vec![None; self.vars.len()];

        if let Some(v) = values {
            if let Ok(dict) = v.cast::<PyDict>() {
                self.fill_from_mapping(dict, &mut slots)?;
            } else if v.is_instance_of::<PyString>() || v.is_instance_of::<PyBytes>() {
                return Err(PyTypeError::new_err(
                    "values must be a mapping of names to integers, or a sequence                      in variable order, not a string",
                ));
            } else if let Ok(seq) = v.cast::<PySequence>() {
                let len = seq.len()?;
                if len != self.vars.len() {
                    return Err(invalid(format!(
                        "expected {} values, one per variable, but got {len}",
                        self.vars.len()
                    ))
                    .into());
                }
                for (i, slot) in slots.iter_mut().enumerate() {
                    let item = seq.get_item(i)?;
                    *slot = Some(extract_masked(&item, self.widths[i])?);
                }
            } else {
                return Err(PyTypeError::new_err(
                    "values must be a mapping of names to integers, or a sequence in variable order",
                ));
            }
        }
        if let Some(kw) = kwargs {
            self.fill_from_mapping(kw, &mut slots)?;
        }

        let mut concrete = Vec::with_capacity(slots.len());
        for (i, slot) in slots.iter().enumerate() {
            match slot {
                Some(v) => concrete.push(*v),
                None => {
                    return Err(
                        invalid(format!("no value given for variable {}", self.vars[i])).into(),
                    )
                }
            }
        }

        let evaluator = self.evaluator()?;
        Ok(evaluator.eval(&concrete))
    }

    /// Evaluate at many points at once.
    ///
    /// The whole run happens in one call with the interpreter lock released,
    /// so this is far quicker than calling `evaluate` in a Python loop. Each
    /// column may be any object supporting the buffer protocol, which covers a
    /// NumPy array and `array.array`, or an ordinary sequence of integers.
    ///
    /// Results come back as a list of integers, or, with `raw=True`, as bytes
    /// holding one little-endian 64-bit value per point. The raw form skips
    /// building a Python integer per result, which is the faster shape when
    /// the values are headed straight back into an array:
    /// `numpy.frombuffer(result, dtype="<u8")`.
    #[pyo3(signature = (values, raw = false))]
    fn evaluate_many(
        &self,
        py: Python<'_>,
        values: &Bound<'_, PyAny>,
        raw: bool,
    ) -> PyResult<Py<PyAny>> {
        if self.vars.is_empty() {
            return Err(invalid(
                "this expression has no variables, so there is nothing to vary; use evaluate()",
            )
            .into());
        }

        let columns = self.read_columns(values)?;
        let points = columns[0].len();

        // Cloning the evaluator is cheap. It is a handle onto the compiled
        // program, and taking one lets the loop run without borrowing back
        // into Python.
        let evaluator = self.evaluator()?.clone();
        let arity = self.vars.len();

        let results = run_detached(py, move || {
            let mut workspace = Workspace::default();
            let mut point = vec![0u64; arity];
            let mut results = Vec::with_capacity(points);
            for index in 0..points {
                for (slot, column) in point.iter_mut().zip(&columns) {
                    *slot = column[index];
                }
                results.push(evaluator.eval_with(&point, &mut workspace));
            }
            results
        })?;

        if raw {
            let mut bytes = Vec::with_capacity(results.len() * 8);
            for value in &results {
                bytes.extend_from_slice(&value.to_le_bytes());
            }
            return Ok(PyBytes::new(py, &bytes).into_any().unbind());
        }
        Ok(PyList::new(py, results)?.into_any().unbind())
    }

    /// The Boolean signature: the expression evaluated over every assignment
    /// of 0 and all-ones to its variables.
    fn signature(&self, py: Python<'_>) -> PyResult<Vec<u64>> {
        let expr = self.expr.clone();
        let num_vars = self.vars.len() as u32;
        let bitwidth = self.bitwidth;
        let sig = run_detached(py, move || {
            try_evaluate_boolean_signature(&expr, num_vars, bitwidth)
        })?;
        Ok(sig.map_err(Error)?)
    }

    /// Run the simplifier over this expression.
    #[pyo3(signature = (options = None))]
    fn simplify(
        slf: &Bound<'_, Self>,
        py: Python<'_>,
        options: Option<&PyOptions>,
    ) -> PyResult<PySimplifyResult> {
        let this = slf.get();
        let opts = match options {
            Some(o) => o.to_rust(),
            // With no options given, run at the width the expression was
            // built at rather than the library default of 64.
            None => cobra::Options {
                bitwidth: this.bitwidth,
                ..cobra::Options::default()
            },
        };
        let expr = this.expr.clone();
        let vars = this.vars.clone();
        let outcome =
            run_detached(py, move || simplify_expr(&expr, &vars, opts))?.map_err(Error)?;
        crate::outcome::build_result(py, &outcome, slf)
    }

    /// A plain-data view of the whole expression, suitable for JSON.
    fn to_dict(&self, py: Python<'_>) -> PyResult<Py<PyDict>> {
        let state = PyDict::new(py);
        state.set_item("bitwidth", self.bitwidth)?;
        state.set_item("variables", self.vars.as_ref().clone())?;
        state.set_item("variable_widths", self.widths.as_ref().clone())?;
        state.set_item("expr", node_to_dict(py, &self.expr, &self.vars, 0)?)?;
        Ok(state.unbind())
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        self.render(py)
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let rendered = self.render(py)?;
        Ok(format!(
            "Expr.parse({rendered:?}, bitwidth={})",
            self.bitwidth
        ))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        match other.extract::<PyRef<'_, Self>>() {
            Ok(o) => {
                self.bitwidth == o.bitwidth
                    && *self.vars == *o.vars
                    && *self.widths == *o.widths
                    && self.expr == o.expr
            }
            Err(_) => false,
        }
    }

    fn __hash__(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.bitwidth.hash(&mut hasher);
        self.vars.hash(&mut hasher);
        self.widths.hash(&mut hasher);
        self.expr.hash(&mut hasher);
        hasher.finish()
    }

    fn __reduce__<'py>(slf: &Bound<'py, Self>, py: Python<'py>) -> PyResult<Bound<'py, PyTuple>> {
        let constructor = slf.get_type().getattr("from_dict")?;
        let state = slf.get().to_dict(py)?;
        let args = PyTuple::new(py, [state.bind(py).as_any()])?;
        PyTuple::new(py, [constructor.as_any(), args.as_any()])
    }

    fn __add__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Add, false)
    }

    fn __radd__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Add, true)
    }

    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Mul, false)
    }

    fn __rmul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Mul, true)
    }

    fn __and__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::And, false)
    }

    fn __rand__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::And, true)
    }

    fn __or__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Or, false)
    }

    fn __ror__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Or, true)
    }

    fn __xor__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Xor, false)
    }

    fn __rxor__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        self.binary(py, other, &SameWidth::Xor, true)
    }

    /// Subtraction lowers to `a + (-b)`, the way the parser lowers `-`.
    fn __sub__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        let Some(rhs) = coerce(other, self)? else {
            return Ok(not_implemented(py));
        };
        let negated = rhs.negate();
        Ok(same_width_op(self, &negated, &SameWidth::Add)?
            .into_pyobject(py)?
            .into_any()
            .unbind())
    }

    fn __rsub__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        let Some(lhs) = coerce(other, self)? else {
            return Ok(not_implemented(py));
        };
        let negated = self.negate();
        Ok(same_width_op(&lhs, &negated, &SameWidth::Add)?
            .into_pyobject(py)?
            .into_any()
            .unbind())
    }

    fn __neg__(&self) -> Self {
        self.negate()
    }

    fn __pos__(&self) -> Self {
        Self::new(
            self.expr.clone(),
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            self.width,
        )
    }

    fn __invert__(&self) -> Self {
        Self::new(
            Expr::not(self.expr.clone()),
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            self.width,
        )
    }

    /// Logical shift right by a literal amount.
    fn __rshift__(&self, amount: u64) -> Result<Self> {
        if amount >= u64::from(self.bitwidth) {
            return Err(invalid(format!(
                "shift amount {amount} out of range for {}-bit mode",
                self.bitwidth
            )));
        }
        Ok(Self::new(
            Expr::shr(self.expr.clone(), amount),
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            self.width,
        ))
    }

    /// Shift left by a literal amount, lowered to multiplication the way the
    /// parser lowers `<<`.
    fn __lshift__(&self, amount: u64) -> Result<Self> {
        if amount >= u64::from(self.bitwidth) {
            return Err(invalid(format!(
                "shift amount {amount} out of range for {}-bit mode",
                self.bitwidth
            )));
        }
        let multiplier = (1u64 << amount) & bitmask(self.bitwidth);
        let rhs = Self::new(
            Expr::constant(multiplier),
            Arc::new(Vec::new()),
            Arc::new(Vec::new()),
            self.bitwidth,
            self.bitwidth,
        );
        same_width_op(self, &rhs, &SameWidth::Mul)
    }

    /// Raise to a literal power, expanded the way the parser expands `**`.
    fn __pow__(
        &self,
        py: Python<'_>,
        exponent: &Bound<'_, PyAny>,
        modulo: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<Py<PyAny>> {
        if modulo.is_some_and(|m| !m.is_none()) {
            return Ok(not_implemented(py));
        }
        let Ok(exp) = exponent.extract::<u64>() else {
            return Ok(not_implemented(py));
        };
        if exp > MAX_EXPONENT {
            return Err(invalid(format!("exponent {exp} exceeds limit {MAX_EXPONENT}")).into());
        }
        let expr = if exp == 0 {
            Expr::constant(1 & bitmask(self.bitwidth))
        } else {
            pow_by_squaring(&self.expr, exp)
        };
        let built = Self::new(
            expr,
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            self.width,
        );
        Ok(built.into_pyobject(py)?.into_any().unbind())
    }
}

impl PyExpr {
    fn negate(&self) -> Self {
        Self::new(
            Expr::neg(self.expr.clone()),
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            self.width,
        )
    }

    fn cast_to(&self, width: u32, kind: Kind) -> Result<Self> {
        if !is_valid_bitwidth(width) {
            return Err(invalid(format!(
                "unsupported cast width {width} (must be in 1..=64)"
            )));
        }
        match &kind {
            Kind::ZExt(_) | Kind::SExt(_) if width < self.width => {
                return Err(invalid(format!(
                    "narrowing extension: {width}-bit target over a {}-bit child",
                    self.width
                )));
            }
            Kind::Trunc(_) if width > self.width => {
                return Err(invalid(format!(
                    "widening truncation: {width}-bit target over a {}-bit child",
                    self.width
                )));
            }
            _ => {}
        }
        let child = self.expr.clone();
        let expr = Arc::new(Expr {
            kind,
            children: std::iter::once(child).collect(),
        });
        Ok(Self::new(
            expr,
            self.vars.clone(),
            self.widths.clone(),
            self.bitwidth,
            width,
        ))
    }

    fn binary(
        &self,
        py: Python<'_>,
        other: &Bound<'_, PyAny>,
        op: &SameWidth,
        reflected: bool,
    ) -> PyResult<Py<PyAny>> {
        let Some(rhs) = coerce(other, self)? else {
            return Ok(not_implemented(py));
        };
        let built = if reflected {
            same_width_op(&rhs, self, op)?
        } else {
            same_width_op(self, &rhs, op)?
        };
        Ok(built.into_pyobject(py)?.into_any().unbind())
    }

    /// Read one column of values per variable, each reduced to its own width.
    fn read_columns(&self, values: &Bound<'_, PyAny>) -> PyResult<Vec<Vec<u64>>> {
        let mut columns: Vec<Option<Vec<u64>>> = vec![None; self.vars.len()];

        if let Ok(mapping) = values.cast::<PyDict>() {
            for (key, column) in mapping.iter() {
                let name: String = key
                    .cast::<PyString>()
                    .map_err(|_| PyTypeError::new_err("variable names must be strings"))?
                    .extract()?;
                let Some(index) = self.vars.iter().position(|v| *v == name) else {
                    return Err(
                        invalid(format!("{name} is not a variable of this expression")).into(),
                    );
                };
                columns[index] = Some(read_column(&column, self.widths[index])?);
            }
        } else if values.is_instance_of::<PyString>() || values.is_instance_of::<PyBytes>() {
            return Err(PyTypeError::new_err(
                "values must be a mapping of names to value columns, or one column per \
                 variable in variable order, not a string",
            ));
        } else if let Ok(sequence) = values.cast::<PySequence>() {
            let len = sequence.len()?;
            if len != self.vars.len() {
                return Err(invalid(format!(
                    "expected {} value columns, one per variable, but got {len}",
                    self.vars.len()
                ))
                .into());
            }
            for (index, slot) in columns.iter_mut().enumerate() {
                let column = sequence.get_item(index)?;
                *slot = Some(read_column(&column, self.widths[index])?);
            }
        } else {
            return Err(PyTypeError::new_err(
                "values must be a mapping of names to value columns, or one column per \
                 variable in variable order",
            ));
        }

        let mut resolved = Vec::with_capacity(columns.len());
        let mut expected: Option<usize> = None;
        for (index, slot) in columns.into_iter().enumerate() {
            let Some(column) = slot else {
                return Err(
                    invalid(format!("no values given for variable {}", self.vars[index])).into(),
                );
            };
            match expected {
                None => expected = Some(column.len()),
                Some(len) if len != column.len() => {
                    return Err(invalid(format!(
                        "every variable needs the same number of points, but {} has {} and an \
                         earlier one has {len}",
                        self.vars[index],
                        column.len()
                    ))
                    .into());
                }
                Some(_) => {}
            }
            resolved.push(column);
        }
        Ok(resolved)
    }

    fn fill_from_mapping(
        &self,
        mapping: &Bound<'_, PyDict>,
        slots: &mut [Option<u64>],
    ) -> PyResult<()> {
        for (key, value) in mapping.iter() {
            let name: String = key
                .cast::<PyString>()
                .map_err(|_| PyTypeError::new_err("variable names must be strings"))?
                .extract()?;
            let Some(index) = self.vars.iter().position(|v| *v == name) else {
                return Err(invalid(format!("{name} is not a variable of this expression")).into());
            };
            slots[index] = Some(extract_masked(&value, self.widths[index])?);
        }
        Ok(())
    }
}

/// Split little-endian 64-bit values out of a byte string.
fn decode_le_u64(bytes: &[u8], mask: u64) -> PyResult<Vec<u64>> {
    if bytes.len() % 8 != 0 {
        return Err(invalid(format!(
            "a raw column must be a whole number of 8-byte values, but this one is {} bytes",
            bytes.len()
        ))
        .into());
    }
    Ok(bytes
        .chunks_exact(8)
        .map(|chunk| {
            u64::from_le_bytes(chunk.try_into().expect("chunks_exact(8) yields 8 bytes")) & mask
        })
        .collect())
}

/// Read one column of values, reduced modulo `2 ** width`.
///
/// The buffer protocol is tried first, which is the fast path for a NumPy
/// array or an `array.array`. Signed 64-bit buffers are accepted too, since
/// that is what `numpy.array([...])` produces by default.
fn read_column(column: &Bound<'_, PyAny>, width: u32) -> PyResult<Vec<u64>> {
    let mask = bitmask(width);

    // Raw bytes are the bulk path: eight little-endian bytes per point, and no
    // Python object is touched per value. `numpy_array.tobytes()` produces it.
    if let Ok(bytes) = column.cast::<PyBytes>() {
        return decode_le_u64(bytes.as_bytes(), mask);
    }
    if let Ok(bytes) = column.cast::<PyByteArray>() {
        return decode_le_u64(&bytes.to_vec(), mask);
    }

    let sequence = column.cast::<PySequence>().map_err(|_| {
        PyTypeError::new_err(
            "each column must be a sequence of integers or a bytes object of \
             little-endian 64-bit values",
        )
    })?;
    let len = sequence.len()?;
    let mut values = Vec::with_capacity(len);
    for index in 0..len {
        let item = sequence.get_item(index)?;
        values.push(extract_masked(&item, width)?);
    }
    Ok(values)
}

/// Balanced `Mul` tree for `base ** exp`, matching the parser's expansion.
fn pow_by_squaring(base: &Expr, exp: u64) -> Arc<Expr> {
    if exp == 1 {
        return base.clone_tree();
    }
    if exp % 2 == 0 {
        let half = pow_by_squaring(base, exp / 2);
        let half_again = half.clone_tree();
        Expr::mul(half, half_again)
    } else {
        let rest = pow_by_squaring(base, exp - 1);
        Expr::mul(rest, base.clone_tree())
    }
}

fn check_identifier(name: &str) -> Result<()> {
    // The tokenizer accepts ASCII `[A-Za-z_][A-Za-z0-9_]*`; a name outside
    // that set would build a tree that cannot be rendered and re-parsed.
    let mut chars = name.bytes();
    let ok = match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == b'_' => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == b'_')
        }
        _ => false,
    };
    if ok {
        Ok(())
    } else {
        Err(invalid(format!(
            "{name:?} is not a usable variable name (expected ASCII letters, \
             digits and underscores, not starting with a digit)"
        )))
    }
}

fn get_item<'py>(dict: &Bound<'py, PyDict>, key: &str) -> PyResult<Bound<'py, PyAny>> {
    dict.get_item(key)?
        .ok_or_else(|| PyTypeError::new_err(format!("missing {key:?} entry")))
}

fn kind_name(kind: &Kind) -> &'static str {
    match kind {
        Kind::Constant(_) => "constant",
        Kind::Variable(_) => "variable",
        Kind::Add => "add",
        Kind::Mul => "mul",
        Kind::And => "and",
        Kind::Or => "or",
        Kind::Xor => "xor",
        Kind::Not => "not",
        Kind::Neg => "neg",
        Kind::Shr(_) => "shr",
        Kind::ZExt(_) => "zext",
        Kind::SExt(_) => "sext",
        Kind::Trunc(_) => "trunc",
        Kind::Concat => "concat",
    }
}

fn node_to_dict<'py>(
    py: Python<'py>,
    expr: &Expr,
    vars: &[String],
    depth: u32,
) -> PyResult<Bound<'py, PyDict>> {
    if depth > MAX_DICT_DEPTH {
        return Err(invalid(format!(
            "expression is deeper than {MAX_DICT_DEPTH} nodes; use render() instead"
        ))
        .into());
    }
    let node = PyDict::new(py);
    node.set_item("kind", kind_name(&expr.kind))?;
    match &expr.kind {
        Kind::Constant(v) => node.set_item("value", *v)?,
        Kind::Variable(i) => {
            node.set_item("index", *i)?;
            if let Some(name) = vars.get(*i as usize) {
                node.set_item("name", name)?;
            }
        }
        Kind::Shr(k) => node.set_item("amount", *k)?,
        Kind::ZExt(w) | Kind::SExt(w) | Kind::Trunc(w) => node.set_item("width", *w)?,
        _ => {}
    }
    if !expr.children.is_empty() {
        let children = PyList::empty(py);
        for child in &expr.children {
            children.append(node_to_dict(py, child, vars, depth + 1)?)?;
        }
        node.set_item("children", children)?;
    }
    Ok(node)
}

fn node_from_dict(node: &Bound<'_, PyDict>, num_vars: usize, depth: u32) -> PyResult<Arc<Expr>> {
    if depth > MAX_DICT_DEPTH {
        return Err(invalid(format!("expression is deeper than {MAX_DICT_DEPTH} nodes")).into());
    }
    let kind: String = get_item(node, "kind")?.extract()?;

    let children: Vec<Arc<Expr>> = match node.get_item("children")? {
        Some(list) => {
            let seq = list.cast_into::<PySequence>().map_err(|_| {
                PyTypeError::new_err("the \"children\" entry must be a sequence of nodes")
            })?;
            let len = seq.len()?;
            let mut out = Vec::with_capacity(len);
            for i in 0..len {
                let item = seq.get_item(i)?;
                let child = item.cast_into::<PyDict>().map_err(|_| {
                    PyTypeError::new_err("every child must be a dict describing a node")
                })?;
                out.push(node_from_dict(&child, num_vars, depth + 1)?);
            }
            out
        }
        None => Vec::new(),
    };

    let payload_u64 = |key: &str| -> PyResult<u64> { get_item(node, key)?.extract() };
    let payload_u32 = |key: &str| -> PyResult<u32> { get_item(node, key)?.extract() };

    let expr = match kind.as_str() {
        "constant" => Expr::constant(payload_u64("value")?),
        "variable" => {
            let index = payload_u32("index")?;
            if index as usize >= num_vars {
                return Err(invalid(format!(
                    "variable index {index} has no entry in a table of {num_vars} names"
                ))
                .into());
            }
            Expr::variable(index)
        }
        "add" => Expr::add(take(&children, 2, "add")?[0].clone(), children[1].clone()),
        "mul" => Expr::mul(take(&children, 2, "mul")?[0].clone(), children[1].clone()),
        "and" => Expr::and(take(&children, 2, "and")?[0].clone(), children[1].clone()),
        "or" => Expr::or(take(&children, 2, "or")?[0].clone(), children[1].clone()),
        "xor" => Expr::xor(take(&children, 2, "xor")?[0].clone(), children[1].clone()),
        "concat" => Expr::concat(
            take(&children, 2, "concat")?[0].clone(),
            children[1].clone(),
        ),
        "not" => Expr::not(take(&children, 1, "not")?[0].clone()),
        "neg" => Expr::neg(take(&children, 1, "neg")?[0].clone()),
        "shr" => Expr::shr(
            take(&children, 1, "shr")?[0].clone(),
            u64::from(payload_u32("amount")?),
        ),
        "zext" => Expr::zext(
            take(&children, 1, "zext")?[0].clone(),
            payload_u32("width")?,
        ),
        "sext" => Expr::sext(
            take(&children, 1, "sext")?[0].clone(),
            payload_u32("width")?,
        ),
        "trunc" => Expr::trunc(
            take(&children, 1, "trunc")?[0].clone(),
            payload_u32("width")?,
        ),
        other => return Err(invalid(format!("unknown node kind {other:?}")).into()),
    };
    Ok(expr)
}

fn take<'a>(children: &'a [Arc<Expr>], want: usize, kind: &str) -> PyResult<&'a [Arc<Expr>]> {
    if children.len() != want {
        return Err(invalid(format!(
            "a {kind} node takes {want} children but got {}",
            children.len()
        ))
        .into());
    }
    Ok(children)
}

/// Register the expression type on the extension module.
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyExpr>()?;
    Ok(())
}
