//! Pass registry: function-pointer table of every pass.
//!
//! arrive in the `cobra-passes` crate; this module owns the trait-
//! object-free dispatch types and exposes an initially-empty registry
//! that passes will register into as they're ported.

use cobra_core::result::Result;

use crate::context::OrchestratorContext;
use crate::enums::{PassId, PassTag, StateKind};
use crate::work_item::{PassResult, WorkItem};

pub type ApplicabilityFn = fn(&WorkItem, &OrchestratorContext) -> bool;

pub type PassFn = fn(&WorkItem, &mut OrchestratorContext) -> Result<PassResult>;

/// Static metadata for one registered pass.
#[derive(Copy, Clone)]
pub struct PassDescriptor {
    pub id: PassId,
    pub consumes: StateKind,
    pub tag: PassTag,
    pub applicable: ApplicabilityFn,
    pub run: PassFn,
}

impl std::fmt::Debug for PassDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PassDescriptor")
            .field("id", &self.id)
            .field("consumes", &self.consumes)
            .field("tag", &self.tag)
            .finish_non_exhaustive()
    }
}

/// Global registry. Filled in once `cobra-passes` exists; until then
/// the slice is empty and the orchestrator's scheduler cannot select
/// anything. Keeping the registry here (rather than on `cobra-passes`)
/// the scheduler `#include "OrchestratorPasses.h"`.
#[must_use]
pub const fn pass_registry() -> &'static [PassDescriptor] {
    // Empty for now — populated in the passes session via a
    // follow-up PR that appends entries in PassId order.
    &[]
}
/// Size of the pass-index lookup table. Matches the 64-bit
/// `attempted_mask` invariant that bounds every `PassId` value to `< 64`,
/// which covers both real passes (`PassId::COUNT`) and pseudo-pass
/// history markers past that boundary.
pub const PASS_INDEX_SIZE: usize = 64;

/// Build a fixed-size lookup table indexed by `PassId::as_u8()`.
///
/// Lets the main loop resolve a `PassId` to its descriptor in O(1)
/// instead of O(n) linear scan per iteration.
#[must_use]
pub fn build_pass_index(registry: &[PassDescriptor]) -> [Option<&PassDescriptor>; PASS_INDEX_SIZE] {
    let mut idx: [Option<&PassDescriptor>; PASS_INDEX_SIZE] = [None; PASS_INDEX_SIZE];
    for desc in registry {
        idx[desc.id.as_u8() as usize] = Some(desc);
    }
    idx
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_registry_for_now() {
        assert_eq!(pass_registry().len(), 0);
    }

    #[test]
    fn pass_descriptor_is_copy() {
        fn assert_copy<T: Copy>() {}
        assert_copy::<PassDescriptor>();
    }
}
