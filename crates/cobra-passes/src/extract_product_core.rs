//! Extract a product-AST core: split the input Add-tree into
//! `Mul(var, var)`-style addends and build their sum as the core.
//! Zero-product cases return `Blocked`; the residual is implicitly
//! `original - core` and is computed downstream by
//! [`crate::passes::decomposition_helpers::build_remainder_evaluator`].

use crate::core::expr::Expr;
use crate::core::pass_contract::{
    ReasonCategory, ReasonCode, ReasonDetail, ReasonDomain, ReasonFrame, SolverResult,
};
use crate::core::result::Result;
use std::sync::Arc;

use crate::orchestrator::{ExtractorKind, OrchestratorContext, PassResult, WorkItem};

use crate::passes::decomposition_engine::{
    extractor_applicable, run_extractor, CoreCandidate, DecompositionContext, Extractor,
};
use crate::passes::decomposition_helpers::split_add_tree;

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

pub struct ProductCoreExtractor;

impl Extractor for ProductCoreExtractor {
    fn kind(&self) -> ExtractorKind {
        ExtractorKind::ProductAst
    }

    fn extract(&self, ctx: &DecompositionContext<'_>) -> SolverResult<CoreCandidate> {
        let Some(expr) = ctx.current_expr else {
            return SolverResult::Inapplicable(reason(
                "no expression provided",
                ReasonCategory::GuardFailed,
                1,
            ));
        };

        let mut products: Vec<&Expr> = Vec::new();
        let mut residual: Vec<Arc<Expr>> = Vec::new();
        split_add_tree(expr, &mut products, &mut residual);

        if products.is_empty() {
            return SolverResult::Blocked(reason(
                "no product terms found in AST",
                ReasonCategory::SearchExhausted,
                2,
            ));
        }

        let mut core = products[0].clone_tree();
        for p in products.iter().skip(1) {
            core = Expr::add(core, (*p).clone_tree());
        }

        SolverResult::Success(CoreCandidate {
            expr: core,
            kind: ExtractorKind::ProductAst,
            degree_used: 0,
            single_product: products.len() == 1,
        })
    }
}

pub fn run_extract_product_core(
    item: &WorkItem,
    ctx: &mut OrchestratorContext,
) -> Result<PassResult> {
    run_extractor(item, ctx, &ProductCoreExtractor)
}

#[must_use]
pub fn applicable(item: &WorkItem, ctx: &OrchestratorContext) -> bool {
    extractor_applicable(item, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::classification::Classification;
    use crate::core::evaluator::Evaluator;
    use crate::core::simplify_outcome::Options;
    use crate::orchestrator::{
        AstPayload, OrchestratorContext, PassDecision, Provenance, StateData, WorkItem,
    };

    fn mk_ctx<'a>(
        expr: &'a Expr,
        vars: &'a [String],
        sig: &'a [u64],
        opts: &'a Options,
    ) -> DecompositionContext<'a> {
        DecompositionContext {
            opts,
            bitwidth: 64,
            evaluator: None,
            vars,
            sig,
            current_expr: Some(expr),
            cls: Box::leak(Box::new(Classification::default())),
        }
    }

    fn sign_flip(var_index: u32) -> Arc<Expr> {
        Expr::add(
            Expr::constant(1),
            Expr::mul(
                Expr::constant(u64::MAX - 1),
                Expr::and(Expr::variable(var_index), Expr::constant(1)),
            ),
        )
    }

    #[test]
    fn extracts_two_products() {
        let expr = Expr::add(
            Expr::add(
                Expr::mul(Expr::variable(0), Expr::variable(1)),
                Expr::constant(5),
            ),
            Expr::mul(Expr::variable(2), Expr::variable(3)),
        );
        let opts = Options::default();
        let vars: Vec<String> = (0..4).map(|i| format!("v{i}")).collect();
        let sig = vec![0u64; 16];
        let ctx = mk_ctx(&expr, &vars, &sig, &opts);
        let SolverResult::Success(core) = ProductCoreExtractor.extract(&ctx) else {
            panic!("expected success");
        };
        assert_eq!(core.kind, ExtractorKind::ProductAst);
        assert!(!core.single_product);
    }

    #[test]
    fn marks_unsplit_product_as_single_product() {
        let expr = Expr::mul(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let opts = Options::default();
        let vars: Vec<String> = (0..3).map(|i| format!("v{i}")).collect();
        let sig = vec![0u64; 8];
        let ctx = mk_ctx(&expr, &vars, &sig, &opts);
        let SolverResult::Success(core) = ProductCoreExtractor.extract(&ctx) else {
            panic!("expected success");
        };
        assert!(core.single_product);
        assert_eq!(*core.expr, *expr);
    }

    #[test]
    fn sign_square_single_product_declines_noop_direct_candidate() {
        let sign = sign_flip(2);
        let expr = Expr::mul(
            Expr::mul(
                Expr::add(Expr::variable(0), Expr::variable(1)),
                sign.clone_tree(),
            ),
            sign,
        );
        let vars = vec!["x1".into(), "x2".into(), "x3".into()];
        let mut ctx = OrchestratorContext::new(Options::default(), vars, 64);
        ctx.evaluator = Some(Evaluator::from_expr(&expr, 64));
        let item = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
            expr,
            classification: None,
            provenance: Provenance::Original,
            solve_ctx: None,
        })));

        let result = run_extract_product_core(&item, &mut ctx).unwrap();
        assert_eq!(result.decision, PassDecision::NotApplicable);
        assert!(result.next.is_empty());
    }

    #[test]
    fn blocks_when_no_products() {
        let expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let opts = Options::default();
        let vars = vec!["x".into(), "y".into()];
        let sig = vec![0u64, 1, 1, 2];
        let ctx = mk_ctx(&expr, &vars, &sig, &opts);
        let out = ProductCoreExtractor.extract(&ctx);
        assert!(matches!(out, SolverResult::Blocked(_)));
    }
}
