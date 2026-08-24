//! Seeding helpers that invoke classifier + lowering passes *before*
//!
//! The scheduler expects every `FoldedAst` work item to already carry
//! a classification and a settled provenance; dispatching `ClassifyAst`
//! or `LowerNotOverArith` from the worklist is *not* one of its routes.
//! seeding.

use crate::core::expr::Expr;
use crate::core::pass_contract::ReasonDetail;
use crate::core::result::Result;
use std::sync::Arc;

use crate::orchestrator::{
    AstPayload, LeanCertificate, OrchestratorContext, PassDecision, PassId, Provenance, StateData,
    WorkItem, Worklist,
};

use crate::passes::atom_identity_rewrite::apply_atom_identities;
use crate::passes::classify_ast::run_classify_ast;
use crate::passes::lower_not_over_arith::run_lower_not_over_arith;
use crate::passes::pattern_matcher::simplify_pattern_subtrees_certified;

/// Seed `worklist` with one or two `FoldedAst` items prepared from
///
/// 1. `RunLowerNotOverArith` runs on the `Original` seed.
///    - If lowering fires, the lowered result becomes the classify
///      target and the original seed is retained (for the semilinear
///      path).
///    - Otherwise the original seed becomes the classify target and
///      its provenance is promoted to `Lowered` so the scheduler
///      treats it identically to the fired case.
/// 2. `RunClassifyAst` runs on the target, stamping
///    `run_metadata.input_classification` and the item's
///    `features.classification`.
/// 3. Items are pushed to the worklist.
///
/// Returns early with an `Err` if any pass surfaces one (neither
/// currently does, but the signature is forward-compatible).
pub fn seed_with_ast(
    input_expr: &Expr,
    ctx: &mut OrchestratorContext,
    worklist: &mut Worklist,
) -> Result<()> {
    // Pre-simplify small subexpressions via pattern-table lookup.
    // Peels off MBA obfuscation layers (e.g., (X+Y+1)+(~X|~Y) → X|Y)
    let (pattern_rewritten, pattern_cert) =
        simplify_pattern_subtrees_certified(Arc::new(input_expr.clone()), ctx.bitwidth);
    // Apply atom-level bitwise identities (e.g. `(A|B)-(A&B) -> A^B`)
    // bottom-up. These hold over arbitrary integer atoms and need to
    // fire at seed time so Linear-classified inputs benefit — the
    // in-pipeline `AtomIdentityRewrite` only runs on exploration
    // candidates.
    let rewritten = apply_atom_identities(pattern_rewritten.clone_tree(), ctx.bitwidth);
    // Detect whether any seed-time rewrite changed the tree. When it
    // did, the seed item already carries a cost-improving, verified
    // rewrite — stamp it so the main loop's exhaustion-path fallback
    // can promote it if the downstream pipeline can't terminate
    // (covers e.g. degenerate PIC shapes that collapse to a single
    // Mul during seed).
    let pattern_rewrite_fired = rewritten.as_ref() != input_expr;
    let seed_lean_certificate = seed_rewrite_certificate(
        input_expr,
        &pattern_rewritten,
        &rewritten,
        ctx.bitwidth,
        pattern_cert,
    );

    // Build the Original-provenance seed.
    let mut seed = WorkItem::new(StateData::FoldedAst(Box::new(AstPayload {
        expr: rewritten,
        classification: None,
        provenance: Provenance::Original,
        solve_ctx: None,
    })));
    seed.features.provenance = Provenance::Original;
    seed.metadata.lean_certificate = seed_lean_certificate;

    // Step 1: LowerNotOverArith on the Original seed.
    let lr = run_lower_not_over_arith(&seed, ctx)?;

    let lowering_fired = lr.decision == PassDecision::Advance && !lr.next.is_empty();
    let classify_target = if lowering_fired {
        ctx.lowering_fired = true;
        // Safe: `Advance + non-empty next` guarantees an item.
        lr.next.into_iter().next().unwrap()
    } else {
        seed.clone()
    };

    // Step 2: ClassifyAst on the target.
    let cr = run_classify_ast(&classify_target, ctx)?;
    let classified = cr
        .next
        .into_iter()
        .next()
        .expect("ClassifyAst emits exactly one item");

    let cls = classified.features.classification;

    // Only safe when the classified target *is* the seed. Lowering rewrites
    // `~E` to `Add(Neg(E), C)`, removing every `Not`, so the lowered and
    // un-lowered trees genuinely classify differently and the lowered verdict
    // must not be stamped onto the retained Original. The fired branch below
    // classifies the seed from its own payload instead.
    if !lowering_fired {
        seed.features.classification = cls;
        if let StateData::FoldedAst(ast) = &mut seed.payload {
            ast.classification = cls;
        }
    }

    // Helper: when `simplify_pattern_subtrees` rewrote the input, stamp
    // the seed item so the main loop's exhaustion-path fallback can
    // recognise it as a cost-improving rewrite. `rewrite_gen = 1`
    // distinguish seed-time rewrites from other transforms.
    let stamp_seed_rewrite = |item: &mut WorkItem| {
        if pattern_rewrite_fired && item.rewrite_gen == 0 {
            item.rewrite_gen = 1;
            item.history.push(PassId::PatternSubtreeRewrite);
        }
    };

    // Step 3: push to the worklist.
    if lowering_fired {
        let mut classified = classified;
        stamp_seed_rewrite(&mut classified);
        worklist.push(classified);

        // Classify the retained Original from its own payload, then apply the
        // same Semilinear guard the no-lowering branch applies. Without the
        // guard the Original pops first (the worklist orders on provenance),
        // burns an expansion and is discarded; worse, a lowered-Semilinear
        // verdict routed the un-lowered payload into SemilinearNormalize.
        let seed_cr = run_classify_ast(&seed, ctx)?;
        let mut seed_item = seed_cr
            .next
            .into_iter()
            .next()
            .expect("ClassifyAst emits exactly one item");
        let seed_cls = seed_item.features.classification;
        if matches!(
            seed_cls,
            Some(c) if c.semantic == crate::core::classification::SemanticClass::Semilinear
        ) {
            stamp_seed_rewrite(&mut seed_item);
            worklist.push(seed_item);
        }
    } else {
        // Lowering was a no-op — promote the classified item to Lowered
        // so the scheduler treats it identically to the fired case.
        let mut classified = classified;
        if let StateData::FoldedAst(ast) = &mut classified.payload {
            ast.provenance = Provenance::Lowered;
        }
        classified.features.provenance = Provenance::Lowered;
        stamp_seed_rewrite(&mut classified);
        worklist.push(classified);

        // Only keep the Original for the semilinear path when it's
        // actually classified as semilinear.
        if matches!(
            cls,
            Some(c) if c.semantic == crate::core::classification::SemanticClass::Semilinear
        ) {
            stamp_seed_rewrite(&mut seed);
            worklist.push(seed);
        }
    }

    // Suppress unused-import warning when the Err arm above is never hit.
    let _ = ReasonDetail::default();
    Ok(())
}

fn seed_rewrite_certificate(
    original: &Expr,
    pattern_rewritten: &Expr,
    rewritten: &Expr,
    bitwidth: u32,
    pattern_cert: Option<LeanCertificate>,
) -> Option<LeanCertificate> {
    if original == rewritten {
        return None;
    }

    let atom_cert = if pattern_rewritten == rewritten {
        None
    } else {
        LeanCertificate::try_single_rewrite_between_64(
            bitwidth,
            pattern_rewritten.clone_tree(),
            rewritten.clone_tree(),
        )
    };

    match (pattern_cert, atom_cert) {
        (Some(pattern), Some(atom)) => pattern
            .merge_step_chain(atom)
            .filter(|cert| cert.matches_endpoints(bitwidth, original, rewritten)),
        (Some(pattern), None) if pattern.matches_endpoints(bitwidth, original, rewritten) => {
            Some(pattern)
        }
        (None, Some(atom)) if atom.matches_endpoints(bitwidth, original, rewritten) => Some(atom),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::classification::SemanticClass;
    use crate::core::simplify_outcome::Options;

    #[test]
    fn seed_with_linear_input_pushes_one_lowered_item() {
        // "x + y" — linear, no Not anywhere → lowering no-op → one
        // classified item promoted to Lowered.
        let expr = Expr::add(Expr::variable(0), Expr::variable(1));
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut worklist = Worklist::new();
        seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

        assert_eq!(worklist.len(), 1);
        assert!(!ctx.lowering_fired);
        assert_eq!(
            ctx.run_metadata.input_classification.semantic,
            SemanticClass::Linear
        );
    }

    #[test]
    fn seed_with_semilinear_input_pushes_two_items() {
        // "(x & 0xFF) + y" — semilinear, no Not → lowering no-op →
        // classified Lowered item + original (for semilinear path).
        let expr = Expr::add(
            Expr::and(Expr::variable(0), Expr::constant(0xFF)),
            Expr::variable(1),
        );
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut worklist = Worklist::new();
        seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

        assert_eq!(worklist.len(), 2);
        assert_eq!(
            ctx.run_metadata.input_classification.semantic,
            SemanticClass::Semilinear
        );
    }

    #[test]
    fn seed_with_not_over_arith_triggers_lowering() {
        // "~(x + 1)" — Not-over-arith fires, so ctx.lowering_fired = true.
        //
        // Only the lowered item is queued. The retained Original is now
        // classified from its own un-lowered payload and kept only when that
        // classifies Semilinear, matching the no-lowering branch. This tree
        // does not, and previously it was queued anyway under the *lowered*
        // tree's classification: it pops first (the worklist orders on
        // provenance), burns an expansion, and is discarded.
        let expr = Expr::not(Expr::add(Expr::variable(0), Expr::constant(1)));
        let mut ctx = OrchestratorContext::new(Options::default(), vec!["x".into()], 8);
        let mut worklist = Worklist::new();
        seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

        assert!(ctx.lowering_fired);
        assert_eq!(worklist.len(), 1);
    }

    #[test]
    fn seed_pattern_rewrite_carries_lean_certificate() {
        let expr = Expr::add(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::or(Expr::variable(0), Expr::variable(1)),
        );
        let mut ctx =
            OrchestratorContext::new(Options::default(), vec!["x".into(), "y".into()], 64);
        let mut worklist = Worklist::new();
        seed_with_ast(&expr, &mut ctx, &mut worklist).unwrap();

        let mut found = false;
        while let Some(item) = worklist.pop() {
            if !item.history.contains(&PassId::PatternSubtreeRewrite) {
                continue;
            }
            found = true;
            let cert = item
                .metadata
                .lean_certificate
                .as_ref()
                .expect("seed rewrite has Lean certificate");
            let StateData::FoldedAst(ast) = &item.payload else {
                panic!("expected folded AST")
            };
            assert!(cert.matches_endpoints(64, &expr, &ast.expr));
            assert!(cert
                .steps
                .iter()
                .any(|step| step.theorem == crate::orchestrator::LeanTheorem::AndOrSumEqAdd64));
        }
        assert!(found, "seed rewrite marker should be present");
    }
}
