import Cobra.Core

namespace Cobra

inductive Opcode where
  | const (value : Nat)
  | var (idx : Nat)
  | add
  | mul
  | band
  | bor
  | bxor
  | bnot
  | neg
  | shr (amount : Nat)
  deriving Repr, DecidableEq

namespace Opcode

def exec (width : Nat) (env : Nat -> BitVec width) : Opcode -> List (BitVec width) -> List (BitVec width)
  | const value, stack => BitVec.ofNat width value :: stack
  | var idx, stack => env idx :: stack
  | add, rhs :: lhs :: rest => (lhs + rhs) :: rest
  | mul, rhs :: lhs :: rest => (lhs * rhs) :: rest
  | band, rhs :: lhs :: rest => (lhs &&& rhs) :: rest
  | bor, rhs :: lhs :: rest => (lhs ||| rhs) :: rest
  | bxor, rhs :: lhs :: rest => (lhs ^^^ rhs) :: rest
  | bnot, value :: rest => (~~~value) :: rest
  | neg, value :: rest => (-value) :: rest
  | shr amount, value :: rest => (value >>> amount) :: rest
  | _, stack => stack

end Opcode

abbrev Program := List Opcode

namespace Program

def eval (width : Nat) (env : Nat -> BitVec width) : Program -> List (BitVec width) -> List (BitVec width)
  | [], stack => stack
  | instr :: rest, stack => eval width env rest (Opcode.exec width env instr stack)

theorem eval_append (width : Nat) (env : Nat -> BitVec width) (p q : Program)
    (stack : List (BitVec width)) :
    eval width env (p ++ q) stack = eval width env q (eval width env p stack) := by
  induction p generalizing stack with
  | nil => rfl
  | cons instr rest ih =>
      simp [eval, ih]

end Program

namespace Expr

def compile : Expr -> Program
  | const value => [Opcode.const value]
  | var idx => [Opcode.var idx]
  | add lhs rhs => compile lhs ++ compile rhs ++ [Opcode.add]
  | mul lhs rhs => compile lhs ++ compile rhs ++ [Opcode.mul]
  | band lhs rhs => compile lhs ++ compile rhs ++ [Opcode.band]
  | bor lhs rhs => compile lhs ++ compile rhs ++ [Opcode.bor]
  | bxor lhs rhs => compile lhs ++ compile rhs ++ [Opcode.bxor]
  | bnot arg => compile arg ++ [Opcode.bnot]
  | neg arg => compile arg ++ [Opcode.neg]
  | shr arg amount => compile arg ++ [Opcode.shr amount]

theorem compile_sound (width : Nat) (env : Nat -> BitVec width) (expr : Expr)
    (stack : List (BitVec width)) :
    Program.eval width env (compile expr) stack = Expr.eval width env expr :: stack := by
  induction expr generalizing stack with
  | const value => rfl
  | var idx => rfl
  | add lhs rhs ih_lhs ih_rhs =>
      simp [compile, Expr.eval, Program.eval_append, ih_lhs, ih_rhs, Program.eval, Opcode.exec]
  | mul lhs rhs ih_lhs ih_rhs =>
      simp [compile, Expr.eval, Program.eval_append, ih_lhs, ih_rhs, Program.eval, Opcode.exec]
  | band lhs rhs ih_lhs ih_rhs =>
      simp [compile, Expr.eval, Program.eval_append, ih_lhs, ih_rhs, Program.eval, Opcode.exec]
  | bor lhs rhs ih_lhs ih_rhs =>
      simp [compile, Expr.eval, Program.eval_append, ih_lhs, ih_rhs, Program.eval, Opcode.exec]
  | bxor lhs rhs ih_lhs ih_rhs =>
      simp [compile, Expr.eval, Program.eval_append, ih_lhs, ih_rhs, Program.eval, Opcode.exec]
  | bnot arg ih =>
      simp [compile, Expr.eval, Program.eval_append, ih, Program.eval, Opcode.exec]
  | neg arg ih =>
      simp [compile, Expr.eval, Program.eval_append, ih, Program.eval, Opcode.exec]
  | shr arg amount ih =>
      simp [compile, Expr.eval, Program.eval_append, ih, Program.eval, Opcode.exec]

end Expr

end Cobra
