//! Structural classifier. Walks an `Expr` bottom-up, tallying
//! variable-dependence, polynomial shape, and a rich
//! [`StructuralFlag`] bitset. Ported from
//! `lib/core/Classifier.cpp::ClassifyNode` + `ClassifyStructural`.

use cobra_core::classification::{Classification, SemanticClass, StructuralFlag};
use cobra_core::expr::{Expr, Kind};

/// Per-node accumulator threaded through the recursion. Matches the
/// C++ anonymous `NodeInfo` struct — the layout stays boolean-per-field
/// to keep the port line-for-line readable alongside the original.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Copy, Debug, Default)]
struct NodeInfo {
    has_var_dep: bool,
    is_polynomial: bool,
    has_const_in_bitwise: bool,
    has_arith_var_dep: bool,
    flags: StructuralFlag,
    /// Bitmask of variable indices currently in scope for a `Mul` chain.
    /// Cleared by any non-Mul operator.
    var_mask: u64,
    /// Highest degree of any single variable observed along a Mul chain.
    max_var_degree: u8,
    has_non_leaf_bitwise: bool,
}

fn classify_node(expr: &Expr) -> NodeInfo {
    match &expr.kind {
        Kind::Constant(_) => NodeInfo::default(),
        Kind::Variable(idx) => NodeInfo {
            has_var_dep: true,
            var_mask: if *idx < 64 { 1u64 << idx } else { 0 },
            max_var_degree: 1,
            ..NodeInfo::default()
        },
        Kind::Mul => classify_mul(&expr.children[0], &expr.children[1]),
        Kind::Add => classify_add(&expr.children[0], &expr.children[1]),
        Kind::Neg => {
            let mut child = classify_node(&expr.children[0]);
            child.has_arith_var_dep = child.has_var_dep || child.has_arith_var_dep;
            child.flags |= StructuralFlag::HAS_ARITHMETIC;
            child
        }
        Kind::And | Kind::Or | Kind::Xor => {
            classify_binary_bitwise(&expr.children[0], &expr.children[1])
        }
        Kind::Not => classify_not(&expr.children[0]),
        Kind::Shr(_) => classify_shr(&expr.children[0]),
    }
}

fn classify_mul(lhs_expr: &Expr, rhs_expr: &Expr) -> NodeInfo {
    let lhs = classify_node(lhs_expr);
    let rhs = classify_node(rhs_expr);

    let mut info = NodeInfo {
        has_var_dep: lhs.has_var_dep || rhs.has_var_dep,
        is_polynomial: lhs.is_polynomial
            || rhs.is_polynomial
            || (lhs.has_var_dep && rhs.has_var_dep),
        has_const_in_bitwise: lhs.has_const_in_bitwise || rhs.has_const_in_bitwise,
        has_arith_var_dep: lhs.has_var_dep
            || rhs.has_var_dep
            || lhs.has_arith_var_dep
            || rhs.has_arith_var_dep,
        flags: lhs.flags | rhs.flags | StructuralFlag::HAS_ARITHMETIC,
        var_mask: lhs.var_mask | rhs.var_mask,
        max_var_degree: lhs.max_var_degree.max(rhs.max_var_degree),
        has_non_leaf_bitwise: lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise,
    };

    if lhs.has_var_dep && rhs.has_var_dep {
        info.flags |= StructuralFlag::HAS_MUL;
    }

    // Degree climbs only when the two operands share variables.
    if (lhs.var_mask & rhs.var_mask) != 0 {
        info.max_var_degree = (i32::from(info.max_var_degree) + 1).min(255) as u8;
    }

    // Mixed-product detection — bitwise-with-var-dep times anything var-dep.
    if (lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise) && lhs.has_var_dep && rhs.has_var_dep
    {
        info.flags |= StructuralFlag::HAS_MIXED_PRODUCT;
    }

    // Mul dominating a bitwise-subtree child is `ArithOverBitwise`.
    if lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise {
        info.flags |= StructuralFlag::HAS_ARITH_OVER_BITWISE;
    }

    // Product-type classification (singleton power vs multilinear vs
    // multivar-high-power). Matches the C++ fallout logic verbatim.
    if lhs.has_var_dep && rhs.has_var_dep {
        let lhs_indet = lhs.var_mask == 0;
        let rhs_indet = rhs.var_mask == 0;
        if lhs_indet || rhs_indet {
            info.flags = info.flags
                & !(StructuralFlag::HAS_SINGLETON_POWER | StructuralFlag::HAS_SINGLETON_POWER_GT2);
            info.flags |= StructuralFlag::HAS_MULTILINEAR_PRODUCT;
        } else {
            let var_count = info.var_mask.count_ones();
            if var_count >= 2 && info.max_var_degree >= 2 {
                info.flags = info.flags
                    & !(StructuralFlag::HAS_SINGLETON_POWER
                        | StructuralFlag::HAS_SINGLETON_POWER_GT2);
                info.flags |= StructuralFlag::HAS_MULTIVAR_HIGH_POWER;
            } else if var_count == 1 && info.max_var_degree >= 2 {
                info.flags |= StructuralFlag::HAS_SINGLETON_POWER;
                if info.max_var_degree > 2 {
                    info.flags |= StructuralFlag::HAS_SINGLETON_POWER_GT2;
                }
            } else if var_count >= 2 {
                info.flags |= StructuralFlag::HAS_MULTILINEAR_PRODUCT;
            }
        }
    }

    info
}

fn classify_add(lhs_expr: &Expr, rhs_expr: &Expr) -> NodeInfo {
    let lhs = classify_node(lhs_expr);
    let rhs = classify_node(rhs_expr);
    let mut info = NodeInfo {
        has_var_dep: lhs.has_var_dep || rhs.has_var_dep,
        is_polynomial: lhs.is_polynomial || rhs.is_polynomial,
        has_const_in_bitwise: lhs.has_const_in_bitwise || rhs.has_const_in_bitwise,
        has_arith_var_dep: lhs.has_var_dep
            || rhs.has_var_dep
            || lhs.has_arith_var_dep
            || rhs.has_arith_var_dep,
        flags: lhs.flags | rhs.flags | StructuralFlag::HAS_ARITHMETIC,
        has_non_leaf_bitwise: lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise,
        // Add breaks Mul chains.
        var_mask: 0,
        max_var_degree: 0,
    };
    if lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise {
        info.flags |= StructuralFlag::HAS_ARITH_OVER_BITWISE;
    }
    info
}

fn classify_binary_bitwise(lhs_expr: &Expr, rhs_expr: &Expr) -> NodeInfo {
    let lhs = classify_node(lhs_expr);
    let rhs = classify_node(rhs_expr);
    let mut info = NodeInfo {
        has_var_dep: lhs.has_var_dep || rhs.has_var_dep,
        is_polynomial: lhs.is_polynomial || rhs.is_polynomial,
        has_arith_var_dep: lhs.has_arith_var_dep || rhs.has_arith_var_dep,
        flags: lhs.flags | rhs.flags | StructuralFlag::HAS_BITWISE,
        has_non_leaf_bitwise: lhs.has_non_leaf_bitwise || rhs.has_non_leaf_bitwise,
        has_const_in_bitwise: lhs.has_const_in_bitwise || rhs.has_const_in_bitwise,
        // And/Or/Xor break Mul chains.
        var_mask: 0,
        max_var_degree: 0,
    };
    if lhs.has_arith_var_dep || rhs.has_arith_var_dep {
        info.flags |= StructuralFlag::HAS_BITWISE_OVER_ARITH;
    }
    if info.has_var_dep {
        info.has_non_leaf_bitwise = true;
    }
    if info.has_var_dep && (!lhs.has_var_dep || !rhs.has_var_dep) {
        info.has_const_in_bitwise = true;
    }
    info
}

fn classify_not(child_expr: &Expr) -> NodeInfo {
    let child = classify_node(child_expr);
    let mut info = NodeInfo {
        has_var_dep: child.has_var_dep,
        is_polynomial: child.is_polynomial,
        has_const_in_bitwise: child.has_const_in_bitwise,
        has_arith_var_dep: child.has_arith_var_dep,
        flags: child.flags | StructuralFlag::HAS_BITWISE,
        has_non_leaf_bitwise: child.has_non_leaf_bitwise,
        var_mask: 0,
        max_var_degree: 0,
    };
    if child.has_arith_var_dep {
        info.flags |= StructuralFlag::HAS_BITWISE_OVER_ARITH;
    }
    if child.has_var_dep {
        info.has_non_leaf_bitwise = true;
    }
    info
}

fn classify_shr(child_expr: &Expr) -> NodeInfo {
    let child = classify_node(child_expr);
    let semilinear = !child.has_arith_var_dep && (child.has_var_dep || child.has_const_in_bitwise);
    NodeInfo {
        has_var_dep: child.has_var_dep,
        is_polynomial: child.is_polynomial,
        has_arith_var_dep: child.has_arith_var_dep,
        flags: child.flags,
        has_non_leaf_bitwise: child.has_non_leaf_bitwise,
        has_const_in_bitwise: semilinear || child.has_const_in_bitwise,
        var_mask: 0,
        max_var_degree: 0,
    }
}

/// Top-level classifier. Picks the semantic class from the accumulated
/// flags: polynomial shape is demoted to `NonPolynomial` when mixed
/// product / bitwise-over-arith / unknown shape is present; otherwise
/// `has_const_in_bitwise` → `Semilinear`, else default `Linear`.
#[must_use]
pub fn classify_structural(expr: &Expr) -> Classification {
    let info = classify_node(expr);
    let semantic = if info.is_polynomial {
        if info.flags.contains(StructuralFlag::HAS_MIXED_PRODUCT)
            || info.flags.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH)
            || info.flags.contains(StructuralFlag::HAS_UNKNOWN_SHAPE)
        {
            SemanticClass::NonPolynomial
        } else {
            SemanticClass::Polynomial
        }
    } else if info.has_const_in_bitwise {
        SemanticClass::Semilinear
    } else {
        SemanticClass::Linear
    };
    Classification {
        semantic,
        flags: info.flags,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_is_linear_no_flags() {
        let c = classify_structural(&Expr::constant(42));
        assert_eq!(c.semantic, SemanticClass::Linear);
        assert_eq!(c.flags, StructuralFlag::NONE);
    }

    #[test]
    fn variable_is_linear_no_flags() {
        let c = classify_structural(&Expr::variable(0));
        assert_eq!(c.semantic, SemanticClass::Linear);
        assert_eq!(c.flags, StructuralFlag::NONE);
    }

    #[test]
    fn add_of_vars_is_linear_arithmetic() {
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        let c = classify_structural(&e);
        assert_eq!(c.semantic, SemanticClass::Linear);
        assert!(c.flags.contains(StructuralFlag::HAS_ARITHMETIC));
        assert!(!c.flags.contains(StructuralFlag::HAS_MUL));
    }

    #[test]
    fn mul_of_two_vars_is_polynomial_with_multilinear() {
        let e = Expr::mul(Expr::variable(0), Expr::variable(1));
        let c = classify_structural(&e);
        assert_eq!(c.semantic, SemanticClass::Polynomial);
        assert!(c.flags.contains(StructuralFlag::HAS_ARITHMETIC));
        assert!(c.flags.contains(StructuralFlag::HAS_MUL));
        assert!(c.flags.contains(StructuralFlag::HAS_MULTILINEAR_PRODUCT));
    }

    #[test]
    fn singleton_power_x_squared() {
        // x * x → Polynomial with SingletonPower (degree 2)
        let e = Expr::mul(Expr::variable(0), Expr::variable(0));
        let c = classify_structural(&e);
        assert_eq!(c.semantic, SemanticClass::Polynomial);
        assert!(c.flags.contains(StructuralFlag::HAS_SINGLETON_POWER));
        assert!(!c.flags.contains(StructuralFlag::HAS_SINGLETON_POWER_GT2));
    }

    #[test]
    fn singleton_power_x_cubed() {
        // x * x * x → SingletonPowerGt2 (degree 3)
        let e = Expr::mul(
            Expr::mul(Expr::variable(0), Expr::variable(0)),
            Expr::variable(0),
        );
        let c = classify_structural(&e);
        assert!(c.flags.contains(StructuralFlag::HAS_SINGLETON_POWER));
        assert!(c.flags.contains(StructuralFlag::HAS_SINGLETON_POWER_GT2));
    }

    #[test]
    fn bitwise_with_variable_is_bitwise_flag() {
        let e = Expr::and(Expr::variable(0), Expr::variable(1));
        let c = classify_structural(&e);
        assert_eq!(c.semantic, SemanticClass::Linear);
        assert!(c.flags.contains(StructuralFlag::HAS_BITWISE));
    }

    #[test]
    fn bitwise_with_constant_bumps_to_semilinear() {
        // x & 0xFF → Semilinear
        let e = Expr::and(Expr::variable(0), Expr::constant(0xFF));
        let c = classify_structural(&e);
        assert_eq!(c.semantic, SemanticClass::Semilinear);
        assert!(c.flags.contains(StructuralFlag::HAS_BITWISE));
    }

    #[test]
    fn bitwise_over_arith_flags_set() {
        // (x + y) & z — And over Add(var, var)
        let e = Expr::and(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let c = classify_structural(&e);
        assert!(c.flags.contains(StructuralFlag::HAS_BITWISE_OVER_ARITH));
        assert!(c.flags.contains(StructuralFlag::HAS_ARITHMETIC));
    }

    #[test]
    fn mixed_product_flagged() {
        // (x & y) * z — Mul where lhs is non-leaf bitwise
        let e = Expr::mul(
            Expr::and(Expr::variable(0), Expr::variable(1)),
            Expr::variable(2),
        );
        let c = classify_structural(&e);
        assert!(c.flags.contains(StructuralFlag::HAS_MIXED_PRODUCT));
        assert_eq!(c.semantic, SemanticClass::NonPolynomial);
    }
}
