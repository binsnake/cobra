//! Simplifying many expressions at once.
//!
//! Running a corpus through `simplify()` in a Python loop pays the cost of
//! entering and leaving the extension once per item and leaves every core but
//! one idle. This module takes the whole batch across the boundary once, works
//! it on a pool of worker threads with the interpreter lock released, and
//! builds the Python results at the end.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use cobra::core::width::checked_width_of;
use cobra::{parse_to_ast, simplify_expr, ErrorInfo, Expr, Options, SimplifyOutcome};
use pyo3::exceptions::{PyRuntimeError, PyTypeError};
use pyo3::prelude::*;

use crate::errors::{invalid, Error};
use crate::expr::PyExpr;
use crate::options::PyOptions;
use crate::outcome::PySimplifyResult;
use crate::worker::worker_builder;

/// An expression and the variable table it is indexed against, ready to run.
#[derive(Clone)]
struct Prepared {
    expr: Arc<Expr>,
    vars: Arc<Vec<String>>,
    widths: Arc<Vec<u32>>,
    bitwidth: u32,
    width: u32,
}

/// One item of work, taken from Python before the lock is released.
enum Input {
    /// Parsed on the worker thread, so parsing is parallel too.
    Text(String),
    Tree(Prepared),
}

type ItemResult = Result<(Prepared, SimplifyOutcome), ErrorInfo>;

fn run_one(input: &Input, opts: &Options) -> ItemResult {
    let prepared = match input {
        Input::Text(text) => {
            let parsed = parse_to_ast(text, opts.bitwidth)?;
            let width = checked_width_of(&parsed.expr, &parsed.var_widths, opts.bitwidth)?;
            Prepared {
                expr: parsed.expr,
                vars: Arc::new(parsed.vars),
                widths: Arc::new(parsed.var_widths),
                bitwidth: opts.bitwidth,
                width,
            }
        }
        Input::Tree(prepared) => prepared.clone(),
    };
    let outcome = simplify_expr(&prepared.expr, &prepared.vars, opts.clone())?;
    Ok((prepared, outcome))
}

/// Work the queue on `workers` threads and return results in input order.
fn run_pool(inputs: &[Input], opts: &Options, workers: usize) -> PyResult<Vec<ItemResult>> {
    let cursor = AtomicUsize::new(0);

    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let cursor = &cursor;
            let handle = worker_builder()
                .spawn_scoped(scope, move || {
                    let mut done: Vec<(usize, ItemResult)> = Vec::new();
                    loop {
                        let index = cursor.fetch_add(1, Ordering::Relaxed);
                        let Some(input) = inputs.get(index) else {
                            break;
                        };
                        done.push((index, run_one(input, opts)));
                    }
                    done
                })
                .map_err(|e| {
                    PyRuntimeError::new_err(format!("could not start a CoBRA worker thread: {e}"))
                })?;
            handles.push(handle);
        }

        let mut slots: Vec<Option<ItemResult>> = (0..inputs.len()).map(|_| None).collect();
        for handle in handles {
            let done = handle.join().map_err(|_| {
                PyRuntimeError::new_err("the CoBRA simplifier panicked on a worker thread")
            })?;
            for (index, result) in done {
                slots[index] = Some(result);
            }
        }
        Ok(slots
            .into_iter()
            .map(|slot| slot.expect("every index is assigned exactly once"))
            .collect())
    })
}

/// Collect the Python inputs while the lock is still held.
fn collect_inputs(expressions: &Bound<'_, PyAny>, bitwidth: u32) -> PyResult<Vec<Input>> {
    let mut inputs = Vec::new();
    for item in expressions.try_iter()? {
        let item = item?;
        let index = inputs.len();
        if let Ok(expr) = item.extract::<PyRef<'_, PyExpr>>() {
            if expr.bitwidth != bitwidth {
                return Err(invalid(format!(
                    "item {index} is a {}-bit expression but the batch runs at {bitwidth} bits",
                    expr.bitwidth
                ))
                .into());
            }
            inputs.push(Input::Tree(Prepared {
                expr: expr.expr.clone(),
                vars: expr.vars.clone(),
                widths: expr.widths.clone(),
                bitwidth: expr.bitwidth,
                width: expr.width,
            }));
        } else if let Ok(text) = item.extract::<String>() {
            inputs.push(Input::Text(text));
        } else {
            return Err(PyTypeError::new_err(format!(
                "item {index} is a {}, but every item must be a string or an Expr",
                item.get_type().name()?
            )));
        }
    }
    Ok(inputs)
}

fn default_workers(items: usize) -> usize {
    let available = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    available.min(items).max(1)
}

/// Simplify many expressions on a pool of worker threads.
#[pyfunction]
#[pyo3(signature = (expressions, options = None, workers = None, on_error = "raise"))]
pub fn simplify_many(
    py: Python<'_>,
    expressions: &Bound<'_, PyAny>,
    options: Option<&PyOptions>,
    workers: Option<usize>,
    on_error: &str,
) -> PyResult<Vec<Option<PySimplifyResult>>> {
    let raise_on_error = match on_error {
        "raise" => true,
        "none" => false,
        other => {
            return Err(invalid(format!(
                "on_error must be \"raise\" or \"none\", not {other:?}"
            ))
            .into())
        }
    };

    let options = options.cloned().unwrap_or_default();
    let opts = options.to_rust();

    let inputs = collect_inputs(expressions, opts.bitwidth)?;
    if inputs.is_empty() {
        return Ok(Vec::new());
    }

    let workers = match workers {
        Some(0) => return Err(invalid("workers must be at least 1").into()),
        Some(n) => n.min(inputs.len()),
        None => default_workers(inputs.len()),
    };

    let results = py.detach(|| run_pool(&inputs, &opts, workers))?;

    // Results are built in input order, so the error reported first is always
    // the earliest one regardless of which thread hit it.
    let mut out = Vec::with_capacity(results.len());
    for (index, result) in results.into_iter().enumerate() {
        match result {
            Ok((prepared, outcome)) => {
                let original = Bound::new(
                    py,
                    PyExpr::new(
                        prepared.expr,
                        prepared.vars,
                        prepared.widths,
                        prepared.bitwidth,
                        prepared.width,
                    ),
                )?;
                out.push(Some(crate::outcome::build_result(py, &outcome, &original)?));
            }
            Err(info) => {
                if raise_on_error {
                    return Err(Error(ErrorInfo::new(
                        info.code,
                        format!("item {index}: {}", info.message),
                    ))
                    .into());
                }
                out.push(None);
            }
        }
    }
    Ok(out)
}
