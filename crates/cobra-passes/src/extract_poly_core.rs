//! Extract a polynomial core at a specific degree via
//! [`cobra_ir::recover_multivar_poly`] + [`cobra_ir::build_poly_expr`].
//! Gated on `num_vars <= 6` and an available evaluator.
//!
//! Three separate extractors (`PolyCoreD2`, `PolyCoreD3`,
//! `PolyCoreD4`) share the body — degree is a parameter. The top
//! level decomposition engine dispatches all three.

use cobra_core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use cobra_core::result::Result;

use cobra_ir::{build_poly_expr, recover_multivar_poly};
use cobra_orchestrator::{ExtractorKind, OrchestratorContext, PassResult, WorkItem};

use crate::aux_var::eliminate_aux_vars;
use crate::decomposition_engine::{
    extractor_applicable, run_extractor, CoreCandidate, DecompositionContext, Extractor,
};

fn reason(msg: &'static str, category: ReasonCategory, subcode: u16) -> ReasonDetail {
    ReasonDetail {
        top: ReasonFrame {
            code: ReasonCode {
                category,
                domain: ReasonDomain::Decomposition,
                subcode,
            },
            message: msg.to_string(),
            fields: Vec::new(),
        },
        causes: Vec::new(),
    }
}

pub struct PolyCoreExtractor {
    pub degree: u8,
}

impl PolyCoreExtractor {
    #[must_use]
    pub fn d2() -> Self {
        Self { degree: 2 }
    }
    #[must_use]
    pub fn d3() -> Self {
        Self { degree: 3 }
    }
    #[must_use]
    pub fn d4() -> Self {
        Self { degree: 4 }
    }
}

impl Extractor for PolyCoreExtractor {
    fn kind(&self) -> ExtractorKind {
        ExtractorKind::Polynomial
    }

    fn extract(&self, ctx: &DecompositionContext<'_>) -> SolverResult<CoreCandidate> {
        let Some(eval) = ctx.evaluator else {
            return SolverResult::Inapplicable(reason(
                "polynomial extraction requires evaluator",
                ReasonCategory::GuardFailed,
                3,
            ));
        };

        let num_vars = ctx.vars.len() as u32;

        // Full-width aux-var elimination to discover support.
        let fw_elim = eliminate_aux_vars(ctx.sig, ctx.vars);
        let real_count = fw_elim.real_vars.len() as u32;
        if real_count > 6 {
            return SolverResult::Inapplicable(reason(
                "too many real variables for polynomial extraction",
                ReasonCategory::GuardFailed,
                4,
            ));
        }

        // Build variable-index support from `real_vars` names.
        let support: Vec<u32> = fw_elim
            .real_vars
            .iter()
            .filter_map(|name| ctx.vars.iter().position(|v| v == name).map(|i| i as u32))
            .collect();
        if support.is_empty() {
            return SolverResult::Inapplicable(reason(
                "empty support after aux-var elimination",
                ReasonCategory::GuardFailed,
                5,
            ));
        }

        let poly = recover_multivar_poly(eval, &support, num_vars, ctx.bitwidth, self.degree);
        let Some(payload) = poly.take_payload() else {
            return SolverResult::Blocked(reason(
                "polynomial recovery failed",
                ReasonCategory::SearchExhausted,
                6,
            ));
        };

        let Ok(built) = build_poly_expr(&payload) else {
            return SolverResult::Blocked(reason(
                "expression build from polynomial failed",
                ReasonCategory::SearchExhausted,
                7,
            ));
        };

        SolverResult::Success(CoreCandidate {
            expr: built,
            kind: ExtractorKind::Polynomial,
            degree_used: self.degree,
        })
    }
}

pub fn run_extract_poly_core_d2(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_extractor(item, ctx, &PolyCoreExtractor::d2())
}

pub fn run_extract_poly_core_d3(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_extractor(item, ctx, &PolyCoreExtractor::d3())
}

pub fn run_extract_poly_core_d4(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_extractor(item, ctx, &PolyCoreExtractor::d4())
}

#[must_use]
pub fn applicable(item: &WorkItem, ctx: &OrchestratorContext) -> bool {
    extractor_applicable(item, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cobra_core::classification::Classification;
    use cobra_core::evaluator::Evaluator;
    use cobra_core::expr::Expr;
    use cobra_core::simplify_outcome::Options;

    #[test]
    fn poly_d2_recovers_quadratic() {
        // f(x, y) = x*y + x² — recoverable at degree 2.
        let expr = Expr::add(
            Expr::mul(Expr::variable(0), Expr::variable(1)),
            Expr::mul(Expr::variable(0), Expr::variable(0)),
        );
        let eval = Evaluator::from_expr(&expr, 64);
        let opts = Options::default();
        let vars = vec!["x".into(), "y".into()];
        let sig = vec![0u64, 1, 0, 2];
        let cls = Classification::default();
        let ctx = DecompositionContext {
            opts: &opts,
            bitwidth: 64,
            evaluator: Some(&eval),
            vars: &vars,
            sig: &sig,
            current_expr: Some(&expr),
            cls: &cls,
        };
        let out = PolyCoreExtractor::d2().extract(&ctx);
        assert!(matches!(out, SolverResult::Success(_)));
    }

    #[test]
    fn poly_fails_without_evaluator() {
        let vars = vec!["x".into()];
        let sig = vec![0u64, 1];
        let opts = Options::default();
        let cls = Classification::default();
        let expr = Expr::variable(0);
        let ctx = DecompositionContext {
            opts: &opts,
            bitwidth: 64,
            evaluator: None,
            vars: &vars,
            sig: &sig,
            current_expr: Some(&expr),
            cls: &cls,
        };
        let out = PolyCoreExtractor::d2().extract(&ctx);
        assert!(matches!(out, SolverResult::Inapplicable(_)));
    }
}
