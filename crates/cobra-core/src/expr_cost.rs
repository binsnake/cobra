//! Cost model for ranking candidate simplified expressions.
//!
//! weighted size (favour small trees), non-linear mul count (favour
//! fewer `var * var`), and maximum depth (favour shallow).

use crate::expr::{Expr, Kind};

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ExprCost {
    pub weighted_size: u32,
    pub nonlinear_mul_count: u32,
    pub max_depth: u32,
}

/// Cost plus the var-dependence flag needed to correctly weight `Mul`
/// nodes during recursion.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CostInfo {
    pub cost: ExprCost,
    pub has_var_dep: bool,
}

/// non-linear multiplies (both operands variable-dependent) contribute
/// weight 3 and increment the non-linear-mul counter.
#[must_use]
pub fn compute_cost(expr: &Expr) -> CostInfo {
    match &expr.kind {
        Kind::Constant(_) => CostInfo {
            cost: ExprCost {
                weighted_size: 1,
                nonlinear_mul_count: 0,
                max_depth: 1,
            },
            has_var_dep: false,
        },
        Kind::Variable(_) => CostInfo {
            cost: ExprCost {
                weighted_size: 1,
                nonlinear_mul_count: 0,
                max_depth: 1,
            },
            has_var_dep: true,
        },
        Kind::Not | Kind::Neg | Kind::Shr(_) => {
            let child = compute_cost(&expr.children[0]);
            CostInfo {
                cost: ExprCost {
                    weighted_size: child.cost.weighted_size + 1,
                    nonlinear_mul_count: child.cost.nonlinear_mul_count,
                    max_depth: child.cost.max_depth + 1,
                },
                has_var_dep: child.has_var_dep,
            }
        }
        Kind::Add | Kind::And | Kind::Or | Kind::Xor => {
            let lhs = compute_cost(&expr.children[0]);
            let rhs = compute_cost(&expr.children[1]);
            CostInfo {
                cost: ExprCost {
                    weighted_size: lhs.cost.weighted_size + rhs.cost.weighted_size + 1,
                    nonlinear_mul_count: lhs.cost.nonlinear_mul_count
                        + rhs.cost.nonlinear_mul_count,
                    max_depth: lhs.cost.max_depth.max(rhs.cost.max_depth) + 1,
                },
                has_var_dep: lhs.has_var_dep || rhs.has_var_dep,
            }
        }
        Kind::Mul => {
            let lhs = compute_cost(&expr.children[0]);
            let rhs = compute_cost(&expr.children[1]);
            let nonlinear = lhs.has_var_dep && rhs.has_var_dep;
            let weight: u32 = if nonlinear { 3 } else { 1 };
            let nl_count =
                lhs.cost.nonlinear_mul_count + rhs.cost.nonlinear_mul_count + u32::from(nonlinear);
            CostInfo {
                cost: ExprCost {
                    weighted_size: lhs.cost.weighted_size + rhs.cost.weighted_size + weight,
                    nonlinear_mul_count: nl_count,
                    max_depth: lhs.cost.max_depth.max(rhs.cost.max_depth) + 1,
                },
                has_var_dep: lhs.has_var_dep || rhs.has_var_dep,
            }
        }
    }
}

/// Lexicographic compare: `(weighted_size, nonlinear_mul_count, max_depth)`.
#[inline]
#[must_use]
pub fn is_better(candidate: &ExprCost, baseline: &ExprCost) -> bool {
    (
        candidate.weighted_size,
        candidate.nonlinear_mul_count,
        candidate.max_depth,
    ) < (
        baseline.weighted_size,
        baseline.nonlinear_mul_count,
        baseline.max_depth,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaves_are_size_one_depth_one() {
        let c = compute_cost(&Expr::constant(7));
        assert_eq!(
            c.cost,
            ExprCost {
                weighted_size: 1,
                nonlinear_mul_count: 0,
                max_depth: 1
            }
        );
        assert!(!c.has_var_dep);

        let v = compute_cost(&Expr::variable(0));
        assert_eq!(
            v.cost,
            ExprCost {
                weighted_size: 1,
                nonlinear_mul_count: 0,
                max_depth: 1
            }
        );
        assert!(v.has_var_dep);
    }

    #[test]
    fn add_accumulates_size_and_depth() {
        // (a + b): size = 1 + 1 + 1 = 3, depth = max(1,1)+1 = 2
        let e = Expr::add(Expr::variable(0), Expr::variable(1));
        let c = compute_cost(&e);
        assert_eq!(
            c.cost,
            ExprCost {
                weighted_size: 3,
                nonlinear_mul_count: 0,
                max_depth: 2
            }
        );
        assert!(c.has_var_dep);
    }

    #[test]
    fn linear_mul_has_unit_weight() {
        // c * a: one side constant → linear, weight 1, no nl count
        let e = Expr::mul(Expr::constant(3), Expr::variable(0));
        let c = compute_cost(&e);
        assert_eq!(
            c.cost,
            ExprCost {
                weighted_size: 3,
                nonlinear_mul_count: 0,
                max_depth: 2
            }
        );
    }

    #[test]
    fn nonlinear_mul_has_weight_three_and_counter_increments() {
        // a * b: both var-dep → nonlinear, weight 3, nl count +1
        let e = Expr::mul(Expr::variable(0), Expr::variable(1));
        let c = compute_cost(&e);
        assert_eq!(
            c.cost,
            ExprCost {
                weighted_size: 5,
                nonlinear_mul_count: 1,
                max_depth: 2
            }
        );
    }

    #[test]
    fn nested_nonlinear_mul_accumulates() {
        // (a * b) * c: inner nl (weight 3, nl=1), outer nl (weight 3, nl+=1)
        // weighted_size = 5 + 1 + 3 = 9, nl_count = 2, depth = 3
        let inner = Expr::mul(Expr::variable(0), Expr::variable(1));
        let e = Expr::mul(inner, Expr::variable(2));
        let c = compute_cost(&e);
        assert_eq!(
            c.cost,
            ExprCost {
                weighted_size: 9,
                nonlinear_mul_count: 2,
                max_depth: 3
            }
        );
    }

    #[test]
    fn is_better_is_lexicographic() {
        let small = ExprCost {
            weighted_size: 3,
            nonlinear_mul_count: 0,
            max_depth: 2,
        };
        let big = ExprCost {
            weighted_size: 5,
            nonlinear_mul_count: 0,
            max_depth: 2,
        };
        assert!(is_better(&small, &big));
        assert!(!is_better(&big, &small));

        // Same weighted_size, ties go to nl_count
        let a = ExprCost {
            weighted_size: 5,
            nonlinear_mul_count: 0,
            max_depth: 3,
        };
        let b = ExprCost {
            weighted_size: 5,
            nonlinear_mul_count: 1,
            max_depth: 1,
        };
        assert!(is_better(&a, &b));

        // All ties → not better
        let a = ExprCost {
            weighted_size: 5,
            nonlinear_mul_count: 1,
            max_depth: 3,
        };
        assert!(!is_better(&a, &a));
    }
}
