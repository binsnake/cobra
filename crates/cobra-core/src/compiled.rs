//! Flat stack-machine bytecode for fast repeated evaluation.
//!
//! Ported from `include/cobra/core/CompiledExpr.h` and `lib/core/CompiledExpr.cpp`.
//! The C++ `EvalInstr` re-uses `Expr::Kind` as its opcode tag and a single
//! `uint64_t operand` field. The Rust port separates the flat opcode from the
//! tree-bearing `Kind` so that a compiled instruction doesn't carry redundant
//! payload inside its variant.

use crate::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr};
use crate::expr::{Expr, Kind};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Opcode {
    Constant,
    Variable,
    Add,
    Mul,
    And,
    Or,
    Xor,
    Not,
    Neg,
    Shr,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EvalInstr {
    pub op: Opcode,
    /// `Constant` → value (pre-masked to `bitwidth`);
    /// `Variable` → index into the var-values vector;
    /// `Shr` → shift amount;
    /// all others → 0 (unused).
    pub operand: u64,
}

#[derive(Clone, Debug, Default)]
pub struct CompiledExpr {
    pub bitwidth: u32,
    pub mask: u64,
    /// One past the highest variable index referenced.
    pub arity: u32,
    /// Minimum stack depth required for evaluation. Always `>= 1`.
    pub stack_size: usize,
    pub program: Vec<EvalInstr>,
}

/// Compile an `Expr` tree into flat bytecode.
///
/// Iterative post-order traversal; the frames stack mirrors the C++ version
/// exactly so the emitted instruction sequence is identical.
#[must_use]
pub fn compile(expr: &Expr, bitwidth: u32) -> CompiledExpr {
    struct Frame<'a> {
        node: &'a Expr,
        emit: bool,
    }

    let mask = bitmask(bitwidth);
    let mut compiled = CompiledExpr {
        bitwidth,
        mask,
        arity: 0,
        stack_size: 1,
        program: Vec::with_capacity(64),
    };

    let mut frames: Vec<Frame<'_>> = Vec::with_capacity(64);
    frames.push(Frame {
        node: expr,
        emit: false,
    });

    while let Some(frame) = frames.pop() {
        let node = frame.node;

        if frame.emit {
            // Re-enter: we've already walked the children. Emit the op.
            let (op, operand) = match &node.kind {
                Kind::Constant(v) => (Opcode::Constant, *v),
                Kind::Variable(i) => (Opcode::Variable, u64::from(*i)),
                Kind::Shr(k) => (Opcode::Shr, u64::from(*k)),
                Kind::Not => (Opcode::Not, 0),
                Kind::Neg => (Opcode::Neg, 0),
                Kind::Add => (Opcode::Add, 0),
                Kind::Mul => (Opcode::Mul, 0),
                Kind::And => (Opcode::And, 0),
                Kind::Or => (Opcode::Or, 0),
                Kind::Xor => (Opcode::Xor, 0),
            };
            compiled.program.push(EvalInstr { op, operand });
            continue;
        }

        match &node.kind {
            Kind::Constant(v) => {
                compiled.program.push(EvalInstr {
                    op: Opcode::Constant,
                    operand: *v & mask,
                });
            }
            Kind::Variable(i) => {
                compiled.arity = compiled.arity.max(*i + 1);
                compiled.program.push(EvalInstr {
                    op: Opcode::Variable,
                    operand: u64::from(*i),
                });
            }
            Kind::Not | Kind::Neg | Kind::Shr(_) => {
                frames.push(Frame { node, emit: true });
                frames.push(Frame {
                    node: &node.children[0],
                    emit: false,
                });
            }
            Kind::Add | Kind::Mul | Kind::And | Kind::Or | Kind::Xor => {
                frames.push(Frame { node, emit: true });
                // Push RHS first so LHS is popped (and thus emitted) first — this
                // preserves the same left-to-right ordering as the C++ version.
                frames.push(Frame {
                    node: &node.children[1],
                    emit: false,
                });
                frames.push(Frame {
                    node: &node.children[0],
                    emit: false,
                });
            }
        }
    }

    // Second pass: measure max stack depth required during eval.
    let mut depth: usize = 0;
    let mut max_depth: usize = 0;
    for instr in &compiled.program {
        match instr.op {
            Opcode::Constant | Opcode::Variable => {
                depth += 1;
                if depth > max_depth {
                    max_depth = depth;
                }
            }
            Opcode::Not | Opcode::Neg | Opcode::Shr => {}
            Opcode::Add | Opcode::Mul | Opcode::And | Opcode::Or | Opcode::Xor => {
                depth -= 1;
            }
        }
    }
    compiled.stack_size = if max_depth == 0 { 1 } else { max_depth };
    compiled
}

/// Evaluate a compiled program against `var_values`, using `stack` as a
/// scratch buffer (will be grown if too small). Returns the top-of-stack.
///
/// Ported from `EvalCompiledExpr`. Panics (via index out-of-bounds) on a
/// malformed program — same as the C++ version's unchecked access.
pub fn eval(compiled: &CompiledExpr, var_values: &[u64], stack: &mut Vec<u64>) -> u64 {
    if stack.len() < compiled.stack_size {
        stack.resize(compiled.stack_size, 0);
    }

    let bw = compiled.bitwidth;
    let mask = compiled.mask;
    let mut sp: usize = 0;

    for instr in &compiled.program {
        match instr.op {
            Opcode::Constant => {
                stack[sp] = instr.operand;
                sp += 1;
            }
            Opcode::Variable => {
                stack[sp] = var_values[instr.operand as usize] & mask;
                sp += 1;
            }
            Opcode::Not => {
                stack[sp - 1] = mod_not(stack[sp - 1], bw);
            }
            Opcode::Neg => {
                stack[sp - 1] = mod_neg(stack[sp - 1], bw);
            }
            Opcode::Shr => {
                stack[sp - 1] = mod_shr(stack[sp - 1], instr.operand, bw);
            }
            Opcode::Add => {
                stack[sp - 2] = mod_add(stack[sp - 2], stack[sp - 1], bw);
                sp -= 1;
            }
            Opcode::Mul => {
                stack[sp - 2] = mod_mul(stack[sp - 2], stack[sp - 1], bw);
                sp -= 1;
            }
            Opcode::And => {
                stack[sp - 2] = (stack[sp - 2] & stack[sp - 1]) & mask;
                sp -= 1;
            }
            Opcode::Or => {
                stack[sp - 2] = (stack[sp - 2] | stack[sp - 1]) & mask;
                sp -= 1;
            }
            Opcode::Xor => {
                stack[sp - 2] = (stack[sp - 2] ^ stack[sp - 1]) & mask;
                sp -= 1;
            }
        }
    }

    stack[sp - 1]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(expr: &Expr, bitwidth: u32, vals: &[u64]) -> u64 {
        let c = compile(expr, bitwidth);
        let mut stack = Vec::new();
        eval(&c, vals, &mut stack)
    }

    #[test]
    fn leaves() {
        assert_eq!(run(&Expr::constant(42), 64, &[]), 42);
        assert_eq!(run(&Expr::variable(0), 64, &[7]), 7);
        assert_eq!(run(&Expr::variable(2), 64, &[1, 2, 3]), 3);
    }

    #[test]
    fn constant_masked_at_compile_time() {
        // 0xDEAD at bitwidth 8 should eval to 0xAD
        assert_eq!(run(&Expr::constant(0xDEAD), 8, &[]), 0xAD);
    }

    #[test]
    fn binary_ops_64() {
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        assert_eq!(run(&Expr::add(x.clone(), y.clone()), 64, &[3, 4]), 7);
        assert_eq!(run(&Expr::mul(x.clone(), y.clone()), 64, &[3, 4]), 12);
        assert_eq!(
            run(&Expr::and(x.clone(), y.clone()), 64, &[0xFF, 0x0F]),
            0x0F
        );
        assert_eq!(
            run(&Expr::or(x.clone(), y.clone()), 64, &[0xF0, 0x0F]),
            0xFF
        );
        assert_eq!(
            run(&Expr::xor(x.clone(), y.clone()), 64, &[0xFF, 0x0F]),
            0xF0
        );
    }

    #[test]
    fn unary_ops() {
        assert_eq!(run(&Expr::not(Expr::variable(0)), 8, &[0xF0]), 0x0F);
        assert_eq!(run(&Expr::neg(Expr::variable(0)), 8, &[1]), 0xFF);
        assert_eq!(run(&Expr::shr(Expr::variable(0), 4), 8, &[0xF0]), 0x0F);
    }

    #[test]
    fn nested_expression() {
        // (x & y) + (x | y) should equal x + y for all inputs
        let x = Expr::variable(0);
        let y = Expr::variable(1);
        let expr = Expr::add(
            Expr::and(x.clone(), y.clone()),
            Expr::or(x.clone(), y.clone()),
        );
        let c = compile(&expr, 64);
        let mut stack = Vec::new();
        for (a, b) in [(0u64, 0), (3, 5), (0xFF, 0xAA), (u64::MAX, 1)] {
            assert_eq!(eval(&c, &[a, b], &mut stack), a.wrapping_add(b));
        }
    }

    #[test]
    fn modular_wraps() {
        // 0xFF + 1 at 8-bit should be 0
        let e = Expr::add(Expr::variable(0), Expr::constant(1));
        assert_eq!(run(&e, 8, &[0xFF]), 0);
    }

    #[test]
    fn stack_size_is_minimum() {
        // A long left-leaning chain: ((a+b)+c)+d only needs depth 2
        let e = Expr::add(
            Expr::add(
                Expr::add(Expr::variable(0), Expr::variable(1)),
                Expr::variable(2),
            ),
            Expr::variable(3),
        );
        let c = compile(&e, 64);
        assert!(c.stack_size >= 2, "stack_size = {}", c.stack_size);

        // A balanced tree of depth log2(N) needs more stack
        let e = Expr::add(
            Expr::add(Expr::variable(0), Expr::variable(1)),
            Expr::add(Expr::variable(2), Expr::variable(3)),
        );
        let c = compile(&e, 64);
        assert!(c.stack_size >= 3);
    }

    #[test]
    fn arity_tracks_max_var_index() {
        let e = Expr::add(Expr::variable(0), Expr::variable(2));
        let c = compile(&e, 64);
        assert_eq!(c.arity, 3);

        let e = Expr::constant(7);
        let c = compile(&e, 64);
        assert_eq!(c.arity, 0);
    }
}
