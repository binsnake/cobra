//! Pass registry: function-pointer table of every pass.
//!
//! Matches C++ `lib/core/OrchestratorPasses.h`. Pass implementations
//! arrive in the `cobra-passes` crate; this module owns the trait-
//! object-free dispatch types and exposes an initially-empty registry
//! that passes will register into as they're ported.

use cobra_core::result::Result;

use crate::context::OrchestratorContext;
use crate::enums::{PassId, PassTag, StateKind};
use crate::work_item::{PassResult, WorkItem};

/// `fn` pointer type — cheap dispatch, no vtable. Matches
/// C++ `ApplicabilityFn`.
pub type ApplicabilityFn = fn(&WorkItem, &OrchestratorContext) -> bool;

/// `fn` pointer type for pass bodies. Matches C++ `PassFn`.
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
/// avoids the circular dependency the C++ code works around by having
/// the scheduler `#include "OrchestratorPasses.h"`.
#[must_use]
pub const fn pass_registry() -> &'static [PassDescriptor] {
    // Empty for now — populated in the passes session via a
    // follow-up PR that appends entries in PassId order.
    &[]
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
