import Std.Tactic.BVDecide

namespace Cobra

inductive Expr where
  | const (value : Nat)
  | var (idx : Nat)
  | add (lhs rhs : Expr)
  | mul (lhs rhs : Expr)
  | band (lhs rhs : Expr)
  | bor (lhs rhs : Expr)
  | bxor (lhs rhs : Expr)
  | bnot (arg : Expr)
  | neg (arg : Expr)
  | shr (arg : Expr) (amount : Nat)
  deriving Repr, DecidableEq

namespace Expr

def eval (width : Nat) (env : Nat -> BitVec width) : Expr -> BitVec width
  | const value => BitVec.ofNat width value
  | var idx => env idx
  | add lhs rhs => eval width env lhs + eval width env rhs
  | mul lhs rhs => eval width env lhs * eval width env rhs
  | band lhs rhs => eval width env lhs &&& eval width env rhs
  | bor lhs rhs => eval width env lhs ||| eval width env rhs
  | bxor lhs rhs => eval width env lhs ^^^ eval width env rhs
  | bnot arg => ~~~ eval width env arg
  | neg arg => -eval width env arg
  | shr arg amount => eval width env arg >>> amount

end Expr

def allOnes (width : Nat) : BitVec width :=
  ~~~ (BitVec.ofNat width 0)

theorem bnot_eq_neg_add_mask_64 (x : BitVec 64) :
    ~~~x = -x - 1#_ := by
  bv_decide

theorem bnot_eq_neg_add_all_ones_64 (x : BitVec 64) :
    ~~~x = -x + allOnes 64 := by
  simp [allOnes]
  bv_decide

theorem xor_eq_add_sub_two_mul_and_64 (x y : BitVec 64) :
    x ^^^ y = x + y - (2#64 * (x &&& y)) := by
  bv_decide

theorem or_sub_and_eq_xor_64 (x y : BitVec 64) :
    (x ||| y) - (x &&& y) = x ^^^ y := by
  bv_decide

theorem and_or_sum_eq_add_64 (x y : BitVec 64) :
    (x &&& y) + (x ||| y) = x + y := by
  bv_decide

theorem not_or_sub_not_eq_and_64 (x y : BitVec 64) :
    ((~~~x) ||| y) - (~~~x) = x &&& y := by
  bv_decide

theorem not_or_add_self_add_one_eq_and_64 (x y : BitVec 64) :
    ((~~~x) ||| y) + x + 1#_ = x &&& y := by
  bv_decide

theorem xor_via_or_not_64 (x y : BitVec 64) :
    x - y - (2#64 * (x ||| (~~~y))) - 2#64 = x ^^^ y := by
  bv_decide

theorem add_comm_64 (x y : BitVec 64) :
    x + y = y + x := by
  bv_decide (config := { acNf := true })

theorem add_assoc_64 (x y z : BitVec 64) :
    (x + y) + z = x + (y + z) := by
  bv_decide (config := { acNf := true })

theorem mul_comm_64 (x y : BitVec 64) :
    x * y = y * x := by
  bv_decide (config := { acNf := true })

theorem mul_assoc_64 (x y z : BitVec 64) :
    (x * y) * z = x * (y * z) := by
  bv_decide (config := { acNf := true })

theorem add_zero_64 (x : BitVec 64) :
    x + 0#64 = x := by
  simp

theorem mul_zero_64 (x : BitVec 64) :
    x * 0#64 = 0#64 := by
  simp

theorem mul_one_64 (x : BitVec 64) :
    x * 1#64 = x := by
  simp

theorem zero_add_64 (x : BitVec 64) :
    0#64 + x = x := by
  simp

theorem zero_mul_64 (x : BitVec 64) :
    0#64 * x = 0#64 := by
  simp

theorem one_mul_64 (x : BitVec 64) :
    1#64 * x = x := by
  simp

theorem neg_neg_64 (x : BitVec 64) :
    -(-x) = x := by
  bv_decide

theorem not_not_64 (x : BitVec 64) :
    ~~~(~~~x) = x := by
  bv_decide

theorem and_comm_64 (x y : BitVec 64) :
    x &&& y = y &&& x := by
  bv_decide

theorem or_comm_64 (x y : BitVec 64) :
    x ||| y = y ||| x := by
  bv_decide

theorem xor_comm_64 (x y : BitVec 64) :
    x ^^^ y = y ^^^ x := by
  bv_decide

theorem and_self_64 (x : BitVec 64) :
    x &&& x = x := by
  bv_decide

theorem or_self_64 (x : BitVec 64) :
    x ||| x = x := by
  bv_decide

theorem xor_self_64 (x : BitVec 64) :
    x ^^^ x = 0#64 := by
  bv_decide

theorem xor_zero_64 (x : BitVec 64) :
    x ^^^ 0#64 = x := by
  bv_decide

theorem zero_xor_64 (x : BitVec 64) :
    0#64 ^^^ x = x := by
  bv_decide

theorem and_zero_64 (x : BitVec 64) :
    x &&& 0#64 = 0#64 := by
  bv_decide

theorem zero_and_64 (x : BitVec 64) :
    0#64 &&& x = 0#64 := by
  bv_decide

theorem or_zero_64 (x : BitVec 64) :
    x ||| 0#64 = x := by
  bv_decide

theorem zero_or_64 (x : BitVec 64) :
    0#64 ||| x = x := by
  bv_decide

theorem and_all_ones_64 (x : BitVec 64) :
    x &&& allOnes 64 = x := by
  simp [allOnes]
  bv_decide

theorem all_ones_and_64 (x : BitVec 64) :
    allOnes 64 &&& x = x := by
  simp [allOnes]
  bv_decide

theorem or_all_ones_64 (x : BitVec 64) :
    x ||| allOnes 64 = allOnes 64 := by
  simp [allOnes]
  bv_decide

theorem all_ones_or_64 (x : BitVec 64) :
    allOnes 64 ||| x = allOnes 64 := by
  simp [allOnes]
  bv_decide

theorem demorgan_not_and_64 (x y : BitVec 64) :
    ~~~(x &&& y) = (~~~x) ||| (~~~y) := by
  bv_decide

theorem demorgan_not_or_64 (x y : BitVec 64) :
    ~~~(x ||| y) = (~~~x) &&& (~~~y) := by
  bv_decide

theorem shr_zero_64 (x : BitVec 64) :
    x >>> 0 = x := by
  bv_decide

end Cobra
