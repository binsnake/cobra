//! Focused ports of upstream `test/core/test_simplifier.cpp`.
//!
//! These cover public `Simplify` entry semantics rather than individual pass
//! internals, especially no-AST verification contracts and boundary guards.

use cobra_core::evaluator::Evaluator;
use cobra_core::expr::{render, Expr, Kind};
use cobra_core::expr_cost::{compute_cost, is_better};
use cobra_core::expr_rewrite::try_build_var_support;
use cobra_core::expr_utils::remap_var_indices;
use cobra_core::result::CobraError;
use cobra_core::simplify_outcome::{Options, SimplifyOutcomeKind};
use cobra_core::{eval_expr, evaluate_boolean_signature, full_width_check_eval};
use cobra_parser::parse_to_ast;
use cobra_passes::{simplify, simplify_expr, MAX_INPUT_VARS};

fn names(list: &[&str]) -> Vec<String> {
    list.iter().map(|s| (*s).to_string()).collect()
}

macro_rules! v {
    ($index:expr) => {
        Expr::variable($index)
    };
}

macro_rules! c {
    ($value:expr) => {
        Expr::constant($value)
    };
}

fn rendered(out: &cobra_core::SimplifyOutcome, bitwidth: u32) -> String {
    render(
        out.expr.as_ref().expect("simplified outcome has expr"),
        &out.real_vars,
        bitwidth,
    )
}

fn affine_sig(coeffs: &[u64]) -> Vec<u64> {
    let mut sig = vec![0_u64; 1_usize << coeffs.len()];
    for (i, slot) in sig.iter_mut().enumerate() {
        *slot = coeffs
            .iter()
            .enumerate()
            .map(|(bit, coeff)| coeff * (((i >> bit) & 1) as u64))
            .sum();
    }
    sig
}

fn parsed_expr(input: &str, bitwidth: u32) -> (Box<Expr>, Vec<String>) {
    let parsed = parse_to_ast(input, bitwidth)
        .unwrap_or_else(|err| panic!("failed to parse `{input}` at bitwidth {bitwidth}: {err:?}"));
    (parsed.expr, parsed.vars)
}

fn full_width_expr_case(input: &str, bitwidth: u32, opts: Options) -> cobra_core::SimplifyOutcome {
    let (expr, vars) = parsed_expr(input, bitwidth);
    let out = simplify_expr(&expr, &vars, opts).unwrap_or_else(|err| {
        panic!("simplify failed for `{input}` at bitwidth {bitwidth}: {err:?}")
    });
    assert_eq!(
        out.kind,
        SimplifyOutcomeKind::Simplified,
        "`{input}` did not simplify: {:?}",
        out.diag
    );

    let mut candidate = out
        .expr
        .as_ref()
        .expect("simplified outcome has expr")
        .clone_tree();
    let support = try_build_var_support(&vars, &out.real_vars)
        .unwrap_or_else(|| panic!("cannot remap {:?} into {:?}", out.real_vars, vars));
    remap_var_indices(&mut candidate, &support);

    let eval = Evaluator::from_expr(&expr, bitwidth);
    let check = full_width_check_eval(&eval, vars.len() as u32, &candidate, bitwidth, 512);
    assert!(
        check.passed,
        "`{input}` rendered as `{}` but failed full-width check: {:?}",
        render(&candidate, &vars, bitwidth),
        check.failing_input
    );
    out
}

fn assert_full_width_simplifies(input: &str) -> cobra_core::SimplifyOutcome {
    full_width_expr_case(input, 64, Options::default())
}

#[test]
fn constant_no_ast_without_evaluator_is_unverified() {
    let vars = names(&["x", "y"]);
    let out = simplify(&[42, 42, 42, 42], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "42");
    assert!(!out.verified);
}

#[test]
fn constant_no_ast_with_evaluator_is_verified() {
    let vars = names(&["x", "y"]);
    let opts = Options {
        evaluator: Evaluator::from_closure(|_| 42),
        ..Options::default()
    };
    let out = simplify(&[42, 42, 42, 42], &vars, None, opts).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "42");
    assert!(out.verified);
}

#[test]
fn dirac_signature_without_evaluator_is_not_marked_verified() {
    let vars = names(&["x"]);
    let out = simplify(&[0, 0], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "0");
    assert!(!out.verified);
}

#[test]
fn dirac_signature_with_evaluator_does_not_emit_verified_zero() {
    let vars = names(&["x"]);
    let dirac = Expr::mul(
        Expr::variable(0),
        Expr::add(Expr::variable(0), Expr::neg(Expr::constant(1))),
    );
    let opts = Options {
        evaluator: Evaluator::from_expr(&dirac, 64),
        ..Options::default()
    };
    let out = simplify(&[0, 0], &vars, None, opts).unwrap();
    if out.kind == SimplifyOutcomeKind::Simplified {
        assert!(
            !(out.verified && rendered(&out, 64) == "0"),
            "must not silently accept a full-width Dirac mismatch"
        );
    }
}

#[test]
fn affine_signatures_match_upstream_shapes() {
    let vars = names(&["x", "y", "z"]);
    let out = simplify(&affine_sig(&[3, 5, 7]), &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "3 * x + 5 * y + 7 * z");

    let vars = names(&["x", "y", "z", "w"]);
    let out = simplify(&affine_sig(&[1, 2, 3, 4]), &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "x + 2 * y + 3 * z + 4 * w");
    assert!(out.verified);
}

#[test]
fn no_ast_x_plus_y_and_xor_y_match_upstream_shapes() {
    let vars = names(&["x", "y"]);

    let add = simplify(&[0, 1, 1, 2], &vars, None, Options::default()).unwrap();
    assert_eq!(add.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&add, 64), "x + y");

    let xor = simplify(&[0, 1, 1, 0], &vars, None, Options::default()).unwrap();
    assert_eq!(xor.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&xor, 64), "x ^ y");
}

#[test]
fn non_affine_bitwise_plus_linear_matches_upstream_shape() {
    let mut sig = vec![0_u64; 8];
    for (i, slot) in sig.iter_mut().enumerate() {
        let x = (i & 1) as u64;
        let y = ((i >> 1) & 1) as u64;
        let z = ((i >> 2) & 1) as u64;
        *slot = (x & y) + z;
    }

    let vars = names(&["x", "y", "z"]);
    let out = simplify(&sig, &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(out.verified);
    assert_eq!(rendered(&out, 64), "(x & y) + z");
}

#[test]
fn aux_var_elimination_reports_reduced_signature_vector() {
    let mut sig = vec![0_u64; 16];
    for (i, slot) in sig.iter_mut().enumerate() {
        let x = ((i >> 2) & 1) as u64;
        let y = ((i >> 3) & 1) as u64;
        *slot = x + y;
    }

    let vars = names(&["a0", "a1", "x", "y"]);
    let out = simplify(&sig, &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(out.real_vars, names(&["x", "y"]));
    assert_eq!(out.sig_vector, vec![0, 1, 1, 2]);
}

#[test]
fn bitwidth_variants_match_upstream_public_behavior() {
    let vars = names(&["x", "y"]);

    let out = simplify(
        &[0, 1, 1, 0],
        &vars,
        None,
        Options {
            bitwidth: 1,
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 1), "x ^ y");
    assert!(out.verified);

    let out = simplify(
        &[0, 200, 100, 44],
        &vars,
        None,
        Options {
            bitwidth: 8,
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(out.verified);

    for bitwidth in [16, 32] {
        let out = simplify(
            &[0, 1, 1, 2],
            &vars,
            None,
            Options {
                bitwidth,
                ..Options::default()
            },
        )
        .unwrap();
        assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
        assert_eq!(rendered(&out, bitwidth), "x + y");
        assert!(out.verified);
    }

    let vars = names(&["x", "y", "z"]);
    let mut sig = vec![0_u64; 8];
    for (i, slot) in sig.iter_mut().enumerate() {
        let x = (i & 1) as u64;
        let y = ((i >> 1) & 1) as u64;
        let z = ((i >> 2) & 1) as u64;
        *slot = (x + y + z) & 1;
    }
    let out = simplify(
        &sig,
        &vars,
        None,
        Options {
            bitwidth: 1,
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(out.verified);
}

#[test]
fn scaled_bitwise_signatures_match_upstream_shapes() {
    let vars = names(&["x"]);
    let out = simplify(&[0, 2], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(rendered(&out, 64).contains('2'));
    assert!(out.verified);

    let vars = names(&["x", "y"]);
    let out = simplify(&[0, 0, 0, 8], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(out.verified);
    assert_eq!(rendered(&out, 64), "8 * (x & y)");
}

#[test]
fn polynomial_boolean_match_is_not_enough_without_evaluator() {
    let vars = names(&["x", "y"]);
    let out = simplify(&[0, 0, 0, 1], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "x & y");

    let original = Expr::mul(v!(0), v!(1));
    let eval = Evaluator::from_expr(&original, 64);
    let check = full_width_check_eval(
        &eval,
        2,
        out.expr.as_ref().expect("simplified outcome has expr"),
        64,
        256,
    );
    assert!(!check.passed);
}

#[test]
fn polynomial_targets_recover_with_evaluator() {
    let vars = names(&["x", "y"]);
    let product = Expr::mul(v!(0), v!(1));
    let out = simplify(
        &[0, 0, 0, 1],
        &vars,
        None,
        Options {
            evaluator: Evaluator::from_expr(&product, 64),
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    let check = full_width_check_eval(
        &Evaluator::from_expr(&product, 64),
        2,
        out.expr.as_ref().expect("simplified outcome has expr"),
        64,
        256,
    );
    assert!(check.passed);

    let vars = names(&["x"]);
    let square = Expr::mul(v!(0), v!(0));
    let out = simplify(
        &[0, 1],
        &vars,
        None,
        Options {
            evaluator: Evaluator::from_expr(&square, 64),
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    let check = full_width_check_eval(
        &Evaluator::from_expr(&square, 64),
        1,
        out.expr.as_ref().expect("simplified outcome has expr"),
        64,
        256,
    );
    assert!(check.passed);
}

#[test]
fn mixed_polynomial_target_recovers_with_evaluator() {
    let vars = names(&["x", "y"]);
    let original = Expr::add(
        Expr::add(
            Expr::add(Expr::mul(v!(0), v!(1)), Expr::mul(c!(2), v!(0))),
            Expr::mul(c!(3), v!(1)),
        ),
        c!(1),
    );
    let out = simplify(
        &[1, 3, 4, 7],
        &vars,
        None,
        Options {
            evaluator: Evaluator::from_expr(&original, 64),
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    let check = full_width_check_eval(
        &Evaluator::from_expr(&original, 64),
        2,
        out.expr.as_ref().expect("simplified outcome has expr"),
        64,
        256,
    );
    assert!(check.passed);
}

#[test]
fn null_polynomial_cases_preserve_full_width_semantics() {
    let vars = names(&["x"]);
    let collapsed = Expr::add(
        Expr::mul(c!(5), Expr::mul(v!(0), v!(0))),
        Expr::mul(c!(4), v!(0)),
    );
    let out = simplify(
        &[0, 1],
        &vars,
        None,
        Options {
            bitwidth: 3,
            evaluator: Evaluator::from_expr(&collapsed, 3),
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    for x in 0..8 {
        let actual = eval_expr(
            out.expr.as_ref().expect("simplified outcome has expr"),
            &[x],
            3,
        );
        let expected = (5 * x * x + 4 * x) & 0x7;
        assert_eq!(actual, expected, "x={x}");
    }

    let zero = Expr::add(
        Expr::mul(c!(4), Expr::mul(v!(0), v!(0))),
        Expr::mul(c!(4), v!(0)),
    );
    let out = simplify(
        &[0, 0],
        &vars,
        None,
        Options {
            bitwidth: 3,
            evaluator: Evaluator::from_expr(&zero, 3),
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    for x in 0..8 {
        let actual = eval_expr(
            out.expr.as_ref().expect("simplified outcome has expr"),
            &[x],
            3,
        );
        assert_eq!(actual, 0, "x={x}");
    }
}

#[test]
fn spot_check_false_keeps_no_ast_result_unverified() {
    let vars = names(&["x", "y"]);
    let opts = Options {
        spot_check: false,
        ..Options::default()
    };
    let out = simplify(&[0, 1, 1, 2], &vars, None, opts).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "x + y");
    assert!(!out.verified);
}

#[test]
fn public_boundaries_match_upstream() {
    let vars = names(&["x"]);
    let err = simplify(
        &[0, 1],
        &vars,
        None,
        Options {
            bitwidth: 0,
            ..Options::default()
        },
    )
    .unwrap_err();
    assert_eq!(err.code, CobraError::InvalidArgument);

    let err = simplify(
        &[0, 1],
        &vars,
        None,
        Options {
            bitwidth: 65,
            ..Options::default()
        },
    )
    .unwrap_err();
    assert_eq!(err.code, CobraError::InvalidArgument);

    let too_many: Vec<String> = (0..=MAX_INPUT_VARS).map(|i| format!("x{i}")).collect();
    let err = simplify(&[0, 0], &too_many, None, Options::default()).unwrap_err();
    assert_eq!(err.code, CobraError::TooManyVariables);

    let out = simplify(
        &[0, 1, 1, 2],
        &names(&["x", "y"]),
        None,
        Options {
            max_vars: 2,
            spot_check: false,
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "x + y");

    let err = simplify(
        &[0, 1, 1, 2],
        &names(&["x", "y"]),
        None,
        Options {
            max_vars: 1,
            spot_check: false,
            ..Options::default()
        },
    )
    .unwrap_err();
    assert_eq!(err.code, CobraError::TooManyVariables);
}

#[test]
fn bitwidth_one_ast_path_is_accepted() {
    let expr = Expr::add(Expr::variable(0), Expr::variable(1));
    let vars = names(&["x", "y"]);
    let out = simplify_expr(
        &expr,
        &vars,
        Options {
            bitwidth: 1,
            spot_check: false,
            ..Options::default()
        },
    )
    .unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
}

#[test]
fn dynamic_mask_rejects_shr_optimization_but_still_verifies() {
    let masked = Expr::and(Expr::constant(0xFF), Expr::shr(Expr::variable(0), 1));
    let vars = names(&["x"]);
    let sig = evaluate_boolean_signature(&masked, 1, 64);
    let out = simplify(&sig, &vars, Some(&masked), Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);

    let eval = Evaluator::from_expr(&masked, 64);
    let check = full_width_check_eval(
        &eval,
        1,
        out.expr.as_ref().expect("simplified outcome has expr"),
        64,
        256,
    );
    assert!(check.passed);
}

#[test]
fn all_zero_signature_is_unverified_without_evaluator() {
    let vars = names(&["x", "y"]);
    let out = simplify(&[0, 0, 0, 0], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert_eq!(rendered(&out, 64), "0");
    assert!(!out.verified);
}

#[test]
fn large_constant_no_ast_preserves_value() {
    let big = u64::MAX - 42;
    let vars = names(&["x", "y"]);
    let out = simplify(&[big, big, big, big], &vars, None, Options::default()).unwrap();
    assert_eq!(out.kind, SimplifyOutcomeKind::Simplified);
    assert!(matches!(
        out.expr.as_ref().expect("simplified outcome has expr").kind,
        Kind::Constant(v) if v == big
    ));
}

#[test]
fn upstream_polynomial_and_singleton_power_cases_verify() {
    for input in [
        "x * y",
        "x * x",
        "x * x * x",
        "x * x * x + x * y",
        "x * x + y * y",
        "3 * x * x + 5 * x + 7",
        "x * x * y",
        "a * a * d",
        "(a * a) * (d * d)",
        "(x & y) + x * y",
    ] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }
}

#[test]
fn upstream_mixed_rewrite_and_bitwise_over_poly_cases_verify() {
    for input in [
        "(x & y) * (x | y) + (x & ~y) * (~x & y)",
        "(x + y) & z",
        "d | (c * a)",
        "(d * d) ^ a",
        "((a & b) | (a & ~b)) * b",
        "d | ~(a * b)",
    ] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }

    let out = full_width_expr_case(
        "d | (c * a)",
        64,
        Options {
            enable_bitwise_decomposition: false,
            ..Options::default()
        },
    );
    assert!(out.verified);
}

#[test]
fn upstream_semilinear_and_not_lowering_cases_verify() {
    for input in [
        "1 + (~a & y)",
        "-3 + -3 * (a | y | z)",
        "3 + 3 * b + 2 * x - 4 * (b & x)",
        "2 - a + 2 * y - 2 * (a & y)",
    ] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }

    for input in ["~(b * b)", "~(a + b)"] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }
}

#[test]
fn upstream_product_residual_and_dynamic_mask_cases_verify() {
    let product_residual =
        "(x & y) * (x | y) + (x & ~y) * (~x & y) + ~x - (x | ~y) - 10 * (x & ~y) - 10 * (x & y)";
    let out = assert_full_width_simplifies(product_residual);
    assert!(out.verified);

    let original = parsed_expr(product_residual, 64).0;
    let original_cost = compute_cost(&original).cost;
    let simplified_cost =
        compute_cost(out.expr.as_ref().expect("simplified outcome has expr")).cost;
    assert!(
        is_better(&simplified_cost, &original_cost),
        "product residual case did not improve cost"
    );

    for input in ["0xff & (x + y + (~x | ~y) + 1)", "(x + ~x + 1) & 0xf"] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }

    let (issue9, vars) = parsed_expr("a | ((1 + a) & (2 - a))", 64);
    let out = simplify_expr(&issue9, &vars, Options::default()).unwrap();
    if out.kind == SimplifyOutcomeKind::Simplified {
        let check = full_width_check_eval(
            &Evaluator::from_expr(&issue9, 64),
            vars.len() as u32,
            out.expr.as_ref().expect("simplified outcome has expr"),
            64,
            512,
        );
        assert!(check.passed, "Issue #9 simplified unsafely");
    }
}

#[test]
fn upstream_mixed_product_decomposition_cases_verify() {
    for input in ["(x ^ y) * z", "(x & y) * z", "(e * e) & d"] {
        let out = assert_full_width_simplifies(input);
        assert!(out.verified, "`{input}` was not marked verified");
    }
}

#[test]
fn upstream_semilinear_canonical_forms_match_upstream() {
    let masked_complement = assert_full_width_simplifies("1 + (~a & y)");
    assert_eq!(rendered(&masked_complement, 64), "-(a | ~y)");

    let scaled_complement = assert_full_width_simplifies("-3 + -3 * (a | y | z)");
    assert_eq!(rendered(&scaled_complement, 64), "3 * ~(a | y | z)");

    let xor_combo = assert_full_width_simplifies("3 + 3 * b + 2 * x - 4 * (b & x)");
    let rendered_xor = rendered(&xor_combo, 64);
    assert!(
        rendered_xor.contains('^'),
        "expected XOR canonicalization, got `{rendered_xor}`"
    );

    let or_not_combo = assert_full_width_simplifies("2 - a + 2 * y - 2 * (a & y)");
    let or_not_text = rendered(&or_not_combo, 64);
    assert!(
        or_not_text.contains("a | ~y"),
        "expected OR/NOT canonicalization, got `{or_not_text}`"
    );
}

#[test]
fn upstream_root_not_over_arithmetic_render_forms_match_upstream() {
    for input in ["~(b * b)", "~(a + b)"] {
        let out = assert_full_width_simplifies(input);
        assert!(
            !matches!(
                out.expr.as_ref().expect("simplified outcome has expr").kind,
                Kind::Not
            ),
            "`{input}` kept a root bitwise NOT"
        );
    }
}
