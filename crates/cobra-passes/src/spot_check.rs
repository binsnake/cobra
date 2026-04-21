//! Backward-compatible shim. `full_width_check_eval` and friends live
//! in `cobra-core::spot_check` so that `cobra-orchestrator` (which
//! cannot depend on `cobra-passes`) can verify rewrites at exhaustion
//! time. Re-exported here to keep every pre-existing
//! `cobra_passes::full_width_check_eval` import working unchanged.

pub use cobra_core::spot_check::{
    full_width_check_eval, verify_in_original_space, CheckResult, DEFAULT_NUM_SAMPLES,
};
