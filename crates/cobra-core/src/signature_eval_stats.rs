//! Optional signature-evaluation counters.
//!
//! The C++ implementation compiles these counters in only when
//! `COBRA_SIG_STATS` is defined. The Rust port exposes the same no-op public
//! API by default.

#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub struct SigEvalStats {
    pub calls: u64,
    pub expr_calls: u64,
    pub eval_calls: u64,
    pub total_points: u64,
    pub total_nodes: u64,
    pub total_us: f64,
}

pub fn sig_stats_record_expr(_num_vars: u32, _node_count: u32, _elapsed_us: f64) {}

pub fn sig_stats_record_eval(_num_vars: u32, _elapsed_us: f64) {}

#[must_use]
pub fn sig_stats_snapshot() -> SigEvalStats {
    SigEvalStats::default()
}

pub fn sig_stats_reset() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_op_stats_match_default_contract() {
        sig_stats_record_expr(2, 7, 1.5);
        sig_stats_record_eval(2, 1.0);
        assert_eq!(sig_stats_snapshot(), SigEvalStats::default());
        sig_stats_reset();
        assert_eq!(sig_stats_snapshot(), SigEvalStats::default());
    }
}
