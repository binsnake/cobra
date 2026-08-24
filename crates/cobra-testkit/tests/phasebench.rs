// Scratch phase-resolution bench (temporary, not committed).
use std::time::Instant;

use cobra::core::simplify_outcome::Options;
use cobra::orchestrator::OrchestratorContext;
use cobra::orchestrator::Worklist;
use cobra::parser::parse_to_ast;
use cobra::passes::{seed_with_ast, simplify_pattern_subtrees};

fn time_it<F: FnMut()>(label: &str, iterations: u32, mut f: F) {
    let started = Instant::now();
    for _ in 0..iterations {
        f();
    }
    println!("{label:>34}: {:>9.1?}/call", started.elapsed() / iterations);
}

#[test]
#[ignore = "phase-resolution timing, run explicitly with --ignored --nocapture"]
fn phase_bench() {
    let parsed = parse_to_ast("x + y", 64).expect("parses");
    let expr = parsed.expr.clone_tree();
    let vars = parsed.vars.clone();

    // Warm caches.
    let _ = cobra::simplify_expr(&expr, &vars, Options::default());

    time_it("simplify_expr (total)", 500, || {
        let _ = std::hint::black_box(cobra::simplify_expr(&expr, &vars, Options::default()));
    });

    time_it("simplify_pattern_subtrees", 500, || {
        let _ = std::hint::black_box(simplify_pattern_subtrees(expr.clone_tree(), 64));
    });

    time_it("seed_with_ast (incl. pattern)", 500, || {
        let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
        let mut worklist = Worklist::new();
        let _ = std::hint::black_box(seed_with_ast(&expr, &mut ctx, &mut worklist));
    });

    time_it("context construction only", 500, || {
        let _ = std::hint::black_box(OrchestratorContext::new(
            Options::default(),
            vars.clone(),
            64,
        ));
    });

    time_it("validate + signature", 500, || {
        let _ = std::hint::black_box(cobra::core::try_evaluate_boolean_signature(&expr, 2, 64));
    });

    time_it("main loop (seed + run)", 500, || {
        let mut ctx = OrchestratorContext::new(Options::default(), vars.clone(), 64);
        ctx.original_expr = Some(expr.clone_tree());
        ctx.evaluator = Some(cobra::core::Evaluator::from_expr(&expr, 64));
        ctx.input_sig = cobra::core::evaluate_boolean_signature(&expr, 2, 64);
        let mut worklist = Worklist::new();
        seed_with_ast(&expr, &mut ctx, &mut worklist).expect("seed");
        let mut policy = cobra::orchestrator::OrchestratorPolicy::default();
        let _ = std::hint::black_box(cobra::orchestrator::run_main_loop(
            &mut ctx,
            &mut worklist,
            &mut policy,
            cobra::passes::PASS_REGISTRY,
            Some(&expr),
        ));
    });
}
