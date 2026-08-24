//! Flat stack-machine bytecode for fast repeated evaluation.
//!
//! tree-bearing `Kind` so that a compiled instruction doesn't carry redundant
//! payload inside its variant.

use crate::core::arith::{bitmask, mod_add, mod_mul, mod_neg, mod_not, mod_shr, sext, trunc, zext};
use crate::core::expr::{Expr, Kind};
use crate::core::result::{err, CobraError, Result};
use crate::core::width::validate_widths;

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
    ZExt,
    SExt,
    Trunc,
    Concat,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EvalInstr {
    pub op: Opcode,
    /// `Constant` → value (pre-masked to `bitwidth`);
    /// `Variable` → index into the var-values vector;
    /// `Shr` → shift amount in the low 32 bits, local width in the high 32;
    /// same-width arithmetic/bitwise operators → local result width;
    /// `ZExt`/`Trunc` → target width `w`;
    /// `SExt` → source width in the low 32 bits, target width in the high 32;
    /// `Concat` → low-child width in the low 32 bits, output width in the high 32;
    pub operand: u64,
}

#[derive(Clone, Debug, Default)]
pub struct CompiledExpr {
    pub bitwidth: u32,
    pub mask: u64,
    pub arity: u32,
    /// Minimum stack depth required for evaluation. `compile` always sets
    /// this to `>= 1`; a `CompiledExpr::default()` has `stack_size == 0`
    /// (and an empty program, which `eval` handles by returning 0).
    pub stack_size: usize,
    pub program: Vec<EvalInstr>,
}

/// Compile an `Expr` tree into flat bytecode.
///
/// exactly so the emitted instruction sequence is identical.
/// Map a node to its emit-time `(opcode, operand)`, plus the node's own result
/// width for the caller's width stack.
///
/// `child_widths` holds the already-emitted children's widths, left to right.
/// This used to call `width_of(node, ..)` per node, and `width_of` recurses
/// down the leftmost spine, making `compile` O(nodes x spine) instead of
/// O(nodes). Children are always emitted before their parent, so their widths
/// are known by the time the parent is emitted.
fn emit_op(node: &Expr, bitwidth: u32, child_widths: &[u32]) -> (Opcode, u64, u32) {
    let first = child_widths.first().copied().unwrap_or(bitwidth);
    match &node.kind {
        Kind::Constant(v) => (Opcode::Constant, *v, bitwidth),
        Kind::Variable(i) => (Opcode::Variable, u64::from(*i), bitwidth),
        Kind::Shr(k) => (Opcode::Shr, pack_widths(*k, first), first),
        Kind::Not => (Opcode::Not, u64::from(first), first),
        Kind::Neg => (Opcode::Neg, u64::from(first), first),
        Kind::Add => (Opcode::Add, u64::from(first), first),
        Kind::Mul => (Opcode::Mul, u64::from(first), first),
        Kind::And => (Opcode::And, u64::from(first), first),
        Kind::Or => (Opcode::Or, u64::from(first), first),
        Kind::Xor => (Opcode::Xor, u64::from(first), first),
        Kind::ZExt(w) => (Opcode::ZExt, u64::from(*w), *w),
        Kind::Trunc(w) => (Opcode::Trunc, u64::from(*w), *w),
        Kind::SExt(w) => {
            // Pack the child's source width (low 32) and target (high 32).
            (Opcode::SExt, pack_widths(first, *w), *w)
        }
        Kind::Concat => {
            // Pack the low child's width (low 32) and the output (high 32).
            let low_w = child_widths.get(1).copied().unwrap_or(bitwidth);
            let out_w = first.saturating_add(low_w);
            (Opcode::Concat, pack_widths(low_w, out_w), out_w)
        }
    }
}

/// Compile after validating that every node has a representable width.
///
/// Prefer this over [`compile`] for any tree that did not come from the
/// pipeline's own validated path. [`width_of`] reports an invalid width as 0,
/// and `bitmask(0) == 0` makes every masked operation produce 0 — a compiled
/// program that silently evaluates to zero everywhere, and therefore compares
/// equal to `Expr::constant(0)` at every probe point.
pub fn try_compile(expr: &Expr, bitwidth: u32) -> Result<CompiledExpr> {
    validate_widths(expr, &[], bitwidth)?;
    let compiled = compile(expr, bitwidth);
    if compiled.program.iter().any(instruction_width_is_invalid) {
        return Err(err(
            CobraError::InvalidArgument,
            "compiled program contains a zero-width instruction".to_string(),
        ));
    }
    Ok(compiled)
}

/// `true` if this instruction carries a width payload of 0, which would mask
/// its result to zero.
fn instruction_width_is_invalid(instr: &EvalInstr) -> bool {
    match instr.op {
        // Same-width ops and the two single-width casts carry the result
        // width directly in `operand`.
        Opcode::Not
        | Opcode::Neg
        | Opcode::Add
        | Opcode::Mul
        | Opcode::And
        | Opcode::Or
        | Opcode::Xor
        | Opcode::ZExt
        | Opcode::Trunc => instr.operand == 0,
        // These pack the relevant width into the high half.
        Opcode::Shr | Opcode::Concat => instr.operand >> 32 == 0,
        // `SExt` packs source width low, target width high; both must be set.
        Opcode::SExt => instr.operand >> 32 == 0 || instr.operand.trailing_zeros() >= 32,
        Opcode::Constant | Opcode::Variable => false,
    }
}

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

    let mut width_stack: Vec<u32> = Vec::with_capacity(64);
    let mut frames: Vec<Frame<'_>> = Vec::with_capacity(64);
    frames.push(Frame {
        node: expr,
        emit: false,
    });

    while let Some(frame) = frames.pop() {
        let node = frame.node;

        if frame.emit {
            // Re-enter: we've already walked the children. Emit the op, taking
            // the children's widths off the stack rather than re-deriving them.
            let arity = node.children.len();
            let split = width_stack.len().saturating_sub(arity);
            let (op, operand, node_width) = {
                let child_widths = &width_stack[split..];
                emit_op(node, bitwidth, child_widths)
            };
            width_stack.truncate(split);
            width_stack.push(node_width);
            compiled.program.push(EvalInstr { op, operand });
            continue;
        }

        match &node.kind {
            Kind::Constant(v) => {
                width_stack.push(bitwidth);
                compiled.program.push(EvalInstr {
                    op: Opcode::Constant,
                    operand: *v & mask,
                });
            }
            Kind::Variable(i) => {
                compiled.arity = compiled.arity.max(*i + 1);
                width_stack.push(bitwidth);
                compiled.program.push(EvalInstr {
                    op: Opcode::Variable,
                    operand: u64::from(*i),
                });
            }
            Kind::Not
            | Kind::Neg
            | Kind::Shr(_)
            | Kind::ZExt(_)
            | Kind::SExt(_)
            | Kind::Trunc(_) => {
                frames.push(Frame { node, emit: true });
                frames.push(Frame {
                    node: &node.children[0],
                    emit: false,
                });
            }
            Kind::Add | Kind::Mul | Kind::And | Kind::Or | Kind::Xor | Kind::Concat => {
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
            Opcode::Not
            | Opcode::Neg
            | Opcode::Shr
            | Opcode::ZExt
            | Opcode::SExt
            | Opcode::Trunc => {}
            Opcode::Add | Opcode::Mul | Opcode::And | Opcode::Or | Opcode::Xor | Opcode::Concat => {
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
pub fn eval(compiled: &CompiledExpr, var_values: &[u64], stack: &mut Vec<u64>) -> u64 {
    // An empty program (e.g. `CompiledExpr::default()`) leaves nothing on the
    // stack; indexing `stack[sp - 1]` below would underflow and panic.
    if compiled.program.is_empty() {
        return 0;
    }
    if stack.len() < compiled.stack_size {
        stack.resize(compiled.stack_size, 0);
    }

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
                stack[sp - 1] = mod_not(stack[sp - 1], instr.operand as u32);
            }
            Opcode::Neg => {
                stack[sp - 1] = mod_neg(stack[sp - 1], instr.operand as u32);
            }
            Opcode::Shr => {
                let (amount, local_width) = unpack_widths(instr.operand);
                stack[sp - 1] = mod_shr(stack[sp - 1], u64::from(amount), local_width);
            }
            Opcode::Add => {
                stack[sp - 2] = mod_add(stack[sp - 2], stack[sp - 1], instr.operand as u32);
                sp -= 1;
            }
            Opcode::Mul => {
                stack[sp - 2] = mod_mul(stack[sp - 2], stack[sp - 1], instr.operand as u32);
                sp -= 1;
            }
            Opcode::And => {
                stack[sp - 2] = (stack[sp - 2] & stack[sp - 1]) & bitmask(instr.operand as u32);
                sp -= 1;
            }
            Opcode::Or => {
                stack[sp - 2] = (stack[sp - 2] | stack[sp - 1]) & bitmask(instr.operand as u32);
                sp -= 1;
            }
            Opcode::Xor => {
                stack[sp - 2] = (stack[sp - 2] ^ stack[sp - 1]) & bitmask(instr.operand as u32);
                sp -= 1;
            }
            Opcode::ZExt => {
                // Local width from the operand; ignores the global mask.
                stack[sp - 1] = zext(stack[sp - 1], instr.operand as u32);
            }
            Opcode::Trunc => {
                stack[sp - 1] = trunc(stack[sp - 1], instr.operand as u32);
            }
            Opcode::SExt => {
                let (from, to) = unpack_widths(instr.operand);
                stack[sp - 1] = sext(stack[sp - 1], from, to);
            }
            Opcode::Concat => {
                let (low_w, out_w) = unpack_widths(instr.operand);
                let high = stack[sp - 2];
                let low = stack[sp - 1] & bitmask(low_w);
                stack[sp - 2] = (high.wrapping_shl(low_w) | low) & bitmask(out_w);
                sp -= 1;
            }
        }
    }

    stack[sp - 1]
}

/// Pack two widths into a single `u64` operand: `lo` in the low 32 bits,
/// `hi` in the high 32 bits.
#[inline]
const fn pack_widths(lo: u32, hi: u32) -> u64 {
    (lo as u64) | ((hi as u64) << 32)
}

/// Inverse of [`pack_widths`].
#[inline]
const fn unpack_widths(packed: u64) -> (u32, u32) {
    (packed as u32, (packed >> 32) as u32)
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
    fn cast_and_concat_ops() {
        // zext(a, 16) at global bw 8: a=0xAB masks to 0xAB then zext keeps 0x00AB.
        assert_eq!(run(&Expr::zext(Expr::variable(0), 16), 8, &[0xAB]), 0x00AB);
        // sext(a, 16) where a is an 8-bit var = 0xFF (-1) -> 0xFFFF.
        assert_eq!(run(&Expr::sext(Expr::variable(0), 16), 8, &[0xFF]), 0xFFFF);
        // sext positive stays positive.
        assert_eq!(run(&Expr::sext(Expr::variable(0), 16), 8, &[0x7F]), 0x007F);
        // trunc(a, 8) of a 16-bit var 0xABCD -> 0xCD.
        assert_eq!(run(&Expr::trunc(Expr::variable(0), 8), 16, &[0xABCD]), 0xCD);
        // concat(a:u8, b:u8) -> u16: high a=0x12, low b=0x34 -> 0x1234.
        // Global bw 8 here; the concat opcode uses its own per-node widths.
        let e = Expr::concat(Expr::variable(0), Expr::variable(1));
        assert_eq!(run(&e, 8, &[0x12, 0x34]), 0x1234);
    }

    #[test]
    fn narrow_operations_use_their_declared_local_width() {
        let narrow_add = Expr::add(
            Expr::trunc(Expr::variable(0), 8),
            Expr::trunc(Expr::variable(1), 8),
        );
        assert_eq!(run(&narrow_add, 64, &[255, 255]), 254);

        let widened = Expr::zext(narrow_add, 64);
        assert_eq!(run(&widened, 64, &[255, 255]), 254);

        let narrow_neg = Expr::neg(Expr::trunc(Expr::variable(0), 8));
        assert_eq!(run(&narrow_neg, 64, &[1]), 255);

        let narrow_shift = Expr::shr(Expr::trunc(Expr::variable(0), 8), 4);
        assert_eq!(run(&narrow_shift, 64, &[0x1f0]), 15);
    }

    #[test]
    fn concat_of_zext_matches_arithmetic() {
        // concat(a:u8, b:u8) == zext(a,16)*256 + zext(b,16) for u8 a,b.
        let lhs = Expr::concat(Expr::variable(0), Expr::variable(1));
        let rhs = Expr::add(
            Expr::mul(Expr::zext(Expr::variable(0), 16), Expr::constant(256)),
            Expr::zext(Expr::variable(1), 16),
        );
        let cl = compile(&lhs, 8);
        let cr = compile(&rhs, 16);
        let mut s = Vec::new();
        for (a, b) in [(0u64, 0), (0x12, 0x34), (0xFF, 0xFF), (0x80, 0x01)] {
            assert_eq!(eval(&cl, &[a, b], &mut s), eval(&cr, &[a, b], &mut s));
        }
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
