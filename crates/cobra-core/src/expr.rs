//!
//! as separate fields, with `constant_val` doing double duty for `kShr`
//! into the `Kind` variant where it belongs, so the struct has exactly two
//! fields: the tagged kind and the child list.

use std::fmt::Write as _;

use smallvec::SmallVec;

use crate::arith::{bitmask, sign_bit_mask};

/// Node kind. Variants that carry payload (`Constant`, `Variable`, `Shr`)
/// store it inline instead of in a side channel on the struct.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Constant(u64),
    Variable(u32),
    Add,
    Mul,
    And,
    Or,
    Xor,
    Not,
    Neg,
    /// Logical shift right. The shift amount is pinned here; `>= 64` yields 0
    Shr(u32),
}

impl Kind {
    /// Number of children a node of this kind must have.
    #[inline]
    #[must_use]
    pub const fn arity(&self) -> usize {
        match self {
            Self::Constant(_) | Self::Variable(_) => 0,
            Self::Not | Self::Neg | Self::Shr(_) => 1,
            Self::Add | Self::Mul | Self::And | Self::Or | Self::Xor => 2,
        }
    }

    /// Render precedence, matching `lib/core/Expr.cpp::Precedence`.
    /// Lower number binds tighter (`~`/unary `-` = 1, `|` = 7, loosest).
    /// `0` means "leaf, no parens ever needed". A child with `prec > parent`
    /// binds looser than its parent and needs parens.
    #[inline]
    #[must_use]
    const fn precedence(&self) -> i32 {
        match self {
            Self::Not | Self::Neg => 1,
            Self::Mul => 2,
            Self::Add => 3,
            Self::Shr(_) => 4,
            Self::And => 5,
            Self::Xor => 6,
            Self::Or => 7,
            Self::Constant(_) | Self::Variable(_) => 0,
        }
    }
}

/// Expression tree node. Owns its children via `Box` in a `SmallVec` so that
/// the common binary-op case stays inline (no heap allocation for the vector
/// `std::unique_ptr<Expr>` semantics).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Expr {
    pub kind: Kind,
    pub children: SmallVec<[Box<Expr>; 2]>,
}

impl Expr {
    #[inline]
    #[must_use]
    pub fn constant(val: u64) -> Box<Self> {
        Box::new(Self {
            kind: Kind::Constant(val),
            children: SmallVec::new(),
        })
    }

    #[inline]
    #[must_use]
    pub fn variable(index: u32) -> Box<Self> {
        Box::new(Self {
            kind: Kind::Variable(index),
            children: SmallVec::new(),
        })
    }

    #[inline]
    #[must_use]
    pub fn add(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Self::binary(Kind::Add, lhs, rhs)
    }

    #[inline]
    #[must_use]
    pub fn mul(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Self::binary(Kind::Mul, lhs, rhs)
    }

    #[inline]
    #[must_use]
    pub fn and(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Self::binary(Kind::And, lhs, rhs)
    }

    #[inline]
    #[must_use]
    pub fn or(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Self::binary(Kind::Or, lhs, rhs)
    }

    #[inline]
    #[must_use]
    pub fn xor(lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        Self::binary(Kind::Xor, lhs, rhs)
    }

    #[inline]
    #[must_use]
    pub fn not(operand: Box<Self>) -> Box<Self> {
        Self::unary(Kind::Not, operand)
    }

    #[inline]
    #[must_use]
    pub fn neg(operand: Box<Self>) -> Box<Self> {
        Self::unary(Kind::Neg, operand)
    }

    /// Logical right shift. `amount >= 64` is accepted and will evaluate to 0
    #[inline]
    #[must_use]
    pub fn shr(operand: Box<Self>, amount: u64) -> Box<Self> {
        let amt = u32::try_from(amount).unwrap_or(u32::MAX);
        Self::unary(Kind::Shr(amt), operand)
    }

    fn unary(kind: Kind, child: Box<Self>) -> Box<Self> {
        let mut children: SmallVec<[Box<Self>; 2]> = SmallVec::new();
        children.push(child);
        Box::new(Self { kind, children })
    }

    fn binary(kind: Kind, lhs: Box<Self>, rhs: Box<Self>) -> Box<Self> {
        let mut children: SmallVec<[Box<Self>; 2]> = SmallVec::new();
        children.push(lhs);
        children.push(rhs);
        Box::new(Self { kind, children })
    }

    /// deep copy. `Clone` already does this via `derive(Clone)`; this is
    #[inline]
    #[must_use]
    pub fn clone_tree(&self) -> Box<Self> {
        Box::new(self.clone())
    }
}

/// Render the expression as a human-readable string, using `var_names[var_index]`
/// for variables and modular-arithmetic semantics for negative constants.
///
/// negative-constant rendering rules.
#[must_use]
pub fn render(expr: &Expr, var_names: &[String], bitwidth: u32) -> String {
    let mut out = String::new();
    render_impl(&mut out, expr, var_names, bitwidth, 0);
    out
}

fn render_impl(
    out: &mut String,
    expr: &Expr,
    var_names: &[String],
    bitwidth: u32,
    parent_prec: i32,
) {
    match &expr.kind {
        Kind::Constant(val) => {
            let mask = bitmask(bitwidth);
            let half = sign_bit_mask(bitwidth);
            if half != 0 && *val >= half && *val <= mask {
                let neg = mask.wrapping_sub(*val).wrapping_add(1);
                let _ = write!(out, "-{neg}");
            } else {
                let _ = write!(out, "{val}");
            }
        }
        Kind::Variable(index) => {
            let idx = *index as usize;
            out.push_str(&var_names[idx]);
        }
        Kind::Not => {
            out.push('~');
            render_impl(out, &expr.children[0], var_names, bitwidth, 1);
        }
        Kind::Neg => {
            out.push('-');
            render_impl(out, &expr.children[0], var_names, bitwidth, 1);
        }
        Kind::Shr(amt) => {
            let prec = expr.kind.precedence();
            let needs_parens = prec > parent_prec && parent_prec > 0;
            if needs_parens {
                out.push('(');
            }
            render_impl(out, &expr.children[0], var_names, bitwidth, prec);
            let _ = write!(out, " >> {amt}");
            if needs_parens {
                out.push(')');
            }
        }
        Kind::Add | Kind::Mul | Kind::And | Kind::Or | Kind::Xor => {
            let prec = expr.kind.precedence();
            let needs_parens = prec > parent_prec && parent_prec > 0;
            if needs_parens {
                out.push('(');
            }
            render_impl(out, &expr.children[0], var_names, bitwidth, prec);
            out.push_str(binop_str(&expr.kind));
            render_impl(out, &expr.children[1], var_names, bitwidth, prec);
            if needs_parens {
                out.push(')');
            }
        }
    }
}

const fn binop_str(kind: &Kind) -> &'static str {
    match kind {
        Kind::Add => " + ",
        Kind::Mul => " * ",
        Kind::And => " & ",
        Kind::Or => " | ",
        Kind::Xor => " ^ ",
        _ => " ? ",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: u32) -> Box<Expr> {
        Expr::variable(i)
    }

    fn names(n: usize) -> Vec<String> {
        ('a'..).take(n).map(|c| c.to_string()).collect()
    }

    #[test]
    fn arity_matches_children() {
        assert_eq!(Expr::constant(7).kind.arity(), 0);
        assert_eq!(Expr::variable(0).kind.arity(), 0);
        assert_eq!(Expr::not(v(0)).kind.arity(), 1);
        assert_eq!(Expr::shr(v(0), 3).kind.arity(), 1);
        assert_eq!(Expr::add(v(0), v(1)).kind.arity(), 2);

        for e in [
            Expr::constant(0),
            Expr::variable(0),
            Expr::not(v(0)),
            Expr::shr(v(0), 3),
            Expr::add(v(0), v(1)),
        ] {
            assert_eq!(e.kind.arity(), e.children.len());
        }
    }

    #[test]
    fn clone_tree_is_deep() {
        let a = Expr::add(Expr::mul(v(0), Expr::constant(3)), v(1));
        let b = a.clone_tree();
        assert_eq!(a, b);
        assert!(!std::ptr::eq(a.as_ref(), b.as_ref()));
        assert!(!std::ptr::eq(
            a.children[0].as_ref(),
            b.children[0].as_ref()
        ));
    }

    #[test]
    fn eq_and_hash_structural() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let a = Expr::add(v(0), Expr::constant(1));
        let b = Expr::add(v(0), Expr::constant(1));
        let c = Expr::add(v(0), Expr::constant(2));
        assert_eq!(a, b);
        assert_ne!(a, c);

        let mut ha = DefaultHasher::new();
        a.hash(&mut ha);
        let mut hb = DefaultHasher::new();
        b.hash(&mut hb);
        assert_eq!(ha.finish(), hb.finish());
    }

    #[test]
    fn render_leaves() {
        let vars = names(2);
        assert_eq!(render(&Expr::variable(0), &vars, 64), "a");
        assert_eq!(render(&Expr::variable(1), &vars, 64), "b");
        assert_eq!(render(&Expr::constant(7), &vars, 64), "7");
    }

    #[test]
    fn render_negative_constant_at_bitwidth() {
        let vars = names(0);
        // At bitwidth 8, 0xFF is -1
        assert_eq!(render(&Expr::constant(0xFF), &vars, 8), "-1");
        // At bitwidth 16, 0xFFFE is -2
        assert_eq!(render(&Expr::constant(0xFFFE), &vars, 16), "-2");
        // Positive half
        assert_eq!(render(&Expr::constant(0x7F), &vars, 8), "127");
        // 64-bit -1
        assert_eq!(render(&Expr::constant(u64::MAX), &vars, 64), "-1");
    }

    #[test]
    fn render_precedence_and_parens() {
        let vars = names(3);
        // (x + y) * z — '*' binds tighter than '+', so we need parens around the +
        let expr = Expr::mul(Expr::add(v(0), v(1)), v(2));
        assert_eq!(render(&expr, &vars, 64), "(a + b) * c");

        // x + y * z — no parens
        let expr = Expr::add(v(0), Expr::mul(v(1), v(2)));
        assert_eq!(render(&expr, &vars, 64), "a + b * c");

        // ~x
        assert_eq!(render(&Expr::not(v(0)), &vars, 64), "~a");
        // -(a + b): the unary minus is prec 1, so its child with prec 3 needs parens
        let expr = Expr::neg(Expr::add(v(0), v(1)));
        assert_eq!(render(&expr, &vars, 64), "-(a + b)");
    }

    #[test]
    fn render_shr() {
        let vars = names(1);
        assert_eq!(render(&Expr::shr(v(0), 3), &vars, 64), "a >> 3");
        // add has prec 3, shr has prec 4. Lower = binds tighter, so add
        // binds tighter than shr and doesn't need parens as shr's child.
        let expr = Expr::shr(Expr::add(v(0), Expr::variable(0)), 2);
        assert_eq!(render(&expr, &vars, 64), "a + a >> 2");

        // When shr is the child of mul (prec 2), shr is looser, so it
        // needs parens.
        let expr = Expr::mul(Expr::shr(v(0), 1), Expr::variable(0));
        assert_eq!(render(&expr, &vars, 64), "(a >> 1) * a");
    }

    #[test]
    fn shr_amount_saturates() {
        // The factory accepts u64 but pins to u32::MAX on overflow. Eval
        // would still short-circuit to 0 for any shift >= 64.
        let e = Expr::shr(Expr::variable(0), u64::MAX);
        if let Kind::Shr(amt) = e.kind {
            assert_eq!(amt, u32::MAX);
        } else {
            panic!("expected Shr kind");
        }
    }
}
