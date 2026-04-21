//! Port of C++ `BuildMappedEvaluator`: produces an evaluator whose
//! arity matches the `SignatureSubproblemContext`'s reduced variable
//! count, remapping when necessary.
//!
//! - When the item carries an `evaluator_override` (residual /
//!   lifted-outer children), the override is remapped to
//!   `sub.real_vars` via `sub.original_indices`.
//! - Otherwise the top-level `ctx.evaluator` is remapped the same way.
//! - If the override/global arity already matches the reduced space
//!   (identity map), no wrapping is performed.
//!
//! The returned evaluator uses a scatter-closure when the reduced
//! arity differs from the source; this matches the C++ `Remap`
//! behaviour and avoids the compiled-body-with-empty-input-map
//! pitfall (`eval_compiled`'s shortcut path feeds the caller's slice
//! straight into the compiled program when `input_map` is empty).

use cobra_core::evaluator::{Evaluator, TraceKind};

use cobra_orchestrator::{OrchestratorContext, SignatureSubproblemContext, WorkItem};

fn is_identity_map(idx_map: &[u32], arity: u32) -> bool {
    idx_map.len() as u32 == arity && idx_map.iter().enumerate().all(|(i, &m)| m as usize == i)
}

/// Remap `base` (arity `source_arity`) into a reduced-arity wrapper
/// via a scatter closure — guaranteeing the resulting evaluator pads
/// the input buffer to the source's arity regardless of whether the
/// underlying body is compiled or a closure.
fn remap_via_closure(base: &Evaluator, idx_map: &[u32], source_arity: u32) -> Evaluator {
    let base = base.clone();
    let idx_map: Vec<u32> = idx_map.to_vec();
    let mut buf_size = source_arity as usize;
    for &idx in &idx_map {
        buf_size = buf_size.max(idx as usize + 1);
    }
    Evaluator::from_closure(move |reduced: &[u64]| {
        let mut wide = vec![0u64; buf_size];
        for (i, &dst) in idx_map.iter().enumerate() {
            if let Some(src) = reduced.get(i) {
                wide[dst as usize] = *src;
            }
        }
        base.eval(&wide)
    })
}

#[must_use]
pub fn build_mapped_evaluator(
    ctx: &OrchestratorContext,
    sub: &SignatureSubproblemContext,
    item: &WorkItem,
) -> Option<Evaluator> {
    if let Some(over) = item.evaluator_override.as_ref() {
        let arity = item.evaluator_override_arity;
        if is_identity_map(&sub.original_indices, arity) {
            return Some(over.clone());
        }
        return Some(
            remap_via_closure(over, &sub.original_indices, arity)
                .with_trace(TraceKind::MappedOverride),
        );
    }
    let global = ctx.evaluator.as_ref()?;
    let original_arity = ctx.original_vars.len() as u32;
    if sub.real_vars.len() == ctx.original_vars.len() {
        return Some(global.clone());
    }
    Some(
        remap_via_closure(global, &sub.original_indices, original_arity)
            .with_trace(TraceKind::MappedGlobal),
    )
}
