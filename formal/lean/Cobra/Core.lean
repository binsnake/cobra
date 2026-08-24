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

theorem xor_add_two_mul_and_eq_add_64 (x y : BitVec 64) :
    (x ^^^ y) + (2#64 * (x &&& y)) = x + y := by
  bv_decide

theorem or_sub_and_eq_xor_64 (x y : BitVec 64) :
    (x ||| y) - (x &&& y) = x ^^^ y := by
  bv_decide

theorem and_or_sum_eq_add_64 (x y : BitVec 64) :
    (x &&& y) + (x ||| y) = x + y := by
  bv_decide

theorem two_mul_and_or_sum_eq_two_mul_add_64 (x y : BitVec 64) :
    (2#64 * (x &&& y)) + (2#64 * (x ||| y)) = (2#64 * x) + (2#64 * y) := by
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

theorem xor_and_eq_and_not_64 (x y : BitVec 64) :
    x ^^^ (x &&& y) = x &&& (~~~y) := by
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

theorem mul_add_64 (x y z : BitVec 64) :
    x * (y + z) = x * y + x * z := by
  rw [BitVec.mul_add]

theorem add_mul_64 (x y z : BitVec 64) :
    (x + y) * z = x * z + y * z := by
  rw [BitVec.add_mul]

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

theorem const_3_and_1_64 :
    3#64 &&& 1#64 = 1#64 := by
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

/-! ## Width-parametric pack

    The theorems below are the width-generic counterparts of the `_64` pack.
    Everything here is a pure bitwise or ring identity, so it holds at every
    width and the certificate machinery can cite it at any bitwidth. The
    arithmetic MBA identities (`xor_eq_add_sub_two_mul_and_64` and its family)
    are deliberately absent: those need carry reasoning that `bv_decide` cannot
    discharge without a concrete width. -/

theorem add_zero_w {w : Nat} (x : BitVec w) : x + 0#w = x := by
  simp

theorem zero_add_w {w : Nat} (x : BitVec w) : 0#w + x = x := by
  simp

theorem mul_zero_w {w : Nat} (x : BitVec w) : x * 0#w = 0#w := by
  simp

theorem zero_mul_w {w : Nat} (x : BitVec w) : 0#w * x = 0#w := by
  simp

theorem mul_one_w {w : Nat} (x : BitVec w) : x * 1#w = x := by
  simp

theorem one_mul_w {w : Nat} (x : BitVec w) : 1#w * x = x := by
  simp

theorem neg_neg_w {w : Nat} (x : BitVec w) : -(-x) = x := by
  simp

theorem not_not_w {w : Nat} (x : BitVec w) : ~~~(~~~x) = x := by
  simp

theorem and_self_w {w : Nat} (x : BitVec w) : x &&& x = x := by
  simp

theorem or_self_w {w : Nat} (x : BitVec w) : x ||| x = x := by
  simp

theorem xor_self_w {w : Nat} (x : BitVec w) : x ^^^ x = 0#w := by
  simp

theorem xor_zero_w {w : Nat} (x : BitVec w) : x ^^^ 0#w = x := by
  simp

theorem zero_xor_w {w : Nat} (x : BitVec w) : 0#w ^^^ x = x := by
  simp

theorem and_zero_w {w : Nat} (x : BitVec w) : x &&& 0#w = 0#w := by
  simp

theorem zero_and_w {w : Nat} (x : BitVec w) : 0#w &&& x = 0#w := by
  simp

theorem or_zero_w {w : Nat} (x : BitVec w) : x ||| 0#w = x := by
  simp

theorem zero_or_w {w : Nat} (x : BitVec w) : 0#w ||| x = x := by
  simp

theorem shr_zero_w {w : Nat} (x : BitVec w) : x >>> 0 = x := by
  simp

theorem and_all_ones_w {w : Nat} (x : BitVec w) : x &&& allOnes w = x := by
  simp [allOnes]

theorem all_ones_and_w {w : Nat} (x : BitVec w) : allOnes w &&& x = x := by
  simp [allOnes]

theorem or_all_ones_w {w : Nat} (x : BitVec w) : x ||| allOnes w = allOnes w := by
  simp [allOnes]

theorem all_ones_or_w {w : Nat} (x : BitVec w) : allOnes w ||| x = allOnes w := by
  simp [allOnes]

/-! ### Complement laws, width-generic -/

theorem and_not_self_w {w : Nat} (x : BitVec w) : x &&& (~~~x) = 0#w := by
  simp

theorem not_and_self_w {w : Nat} (x : BitVec w) : (~~~x) &&& x = 0#w := by
  simp

theorem or_not_self_w {w : Nat} (x : BitVec w) : x ||| (~~~x) = allOnes w := by
  simp [allOnes]

theorem not_or_self_w {w : Nat} (x : BitVec w) : (~~~x) ||| x = allOnes w := by
  simp [allOnes]

theorem xor_not_self_w {w : Nat} (x : BitVec w) : x ^^^ (~~~x) = allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [allOnes]
  intro h
  cases hx : x.getLsbD i <;> simp [h, hx]

theorem not_xor_self_w {w : Nat} (x : BitVec w) : (~~~x) ^^^ x = allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [allOnes]
  intro h
  cases hx : x.getLsbD i <;> simp [h, hx]

/-! ### Absorption laws, width-generic -/

theorem and_or_absorb_w {w : Nat} (x y : BitVec w) : x &&& (x ||| y) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h
  simp [h]

theorem and_or_absorb_right_w {w : Nat} (x y : BitVec w) : x &&& (y ||| x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h
  simp [h]

theorem or_and_absorb_w {w : Nat} (x y : BitVec w) : x ||| (x &&& y) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h _
  exact h

theorem or_and_absorb_right_w {w : Nat} (x y : BitVec w) : x ||| (y &&& x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp

theorem and_or_absorb_comm_w {w : Nat} (x y : BitVec w) : (x ||| y) &&& x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h
  simp [h]

theorem and_or_absorb_comm_right_w {w : Nat} (x y : BitVec w) : (y ||| x) &&& x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h
  simp [h]

theorem or_and_absorb_comm_w {w : Nat} (x y : BitVec w) : (x &&& y) ||| x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro _ h _
  exact h

theorem or_and_absorb_comm_right_w {w : Nat} (x y : BitVec w) : (y &&& x) ||| x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp

/-! ### De Morgan, width-generic -/

theorem demorgan_not_and_w {w : Nat} (x y : BitVec w) :
    ~~~(x &&& y) = (~~~x) ||| (~~~y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro h
  simp [h]

theorem demorgan_or_not_not_w {w : Nat} (x y : BitVec w) :
    (~~~x) ||| (~~~y) = ~~~(x &&& y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro h
  simp [h]

theorem demorgan_not_or_w {w : Nat} (x y : BitVec w) :
    ~~~(x ||| y) = (~~~x) &&& (~~~y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro h
  simp [h]

theorem demorgan_and_not_not_w {w : Nat} (x y : BitVec w) :
    (~~~x) &&& (~~~y) = ~~~(x ||| y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  intro h
  simp [h]

/-! ### Complement laws -/

theorem and_not_self_64 (x : BitVec 64) :
    x &&& (~~~x) = 0#64 := by
  bv_decide

theorem not_and_self_64 (x : BitVec 64) :
    (~~~x) &&& x = 0#64 := by
  bv_decide

theorem or_not_self_64 (x : BitVec 64) :
    x ||| (~~~x) = allOnes 64 := by
  simp [allOnes]

theorem not_or_self_64 (x : BitVec 64) :
    (~~~x) ||| x = allOnes 64 := by
  simp [allOnes]

theorem xor_not_self_64 (x : BitVec 64) :
    x ^^^ (~~~x) = allOnes 64 := by
  simp [allOnes]
  bv_decide

theorem not_xor_self_64 (x : BitVec 64) :
    (~~~x) ^^^ x = allOnes 64 := by
  simp [allOnes]
  bv_decide

/-! ### Absorption laws -/

theorem and_or_absorb_64 (x y : BitVec 64) :
    x &&& (x ||| y) = x := by
  bv_decide

theorem and_or_absorb_right_64 (x y : BitVec 64) :
    x &&& (y ||| x) = x := by
  bv_decide

theorem or_and_absorb_64 (x y : BitVec 64) :
    x ||| (x &&& y) = x := by
  bv_decide

theorem or_and_absorb_right_64 (x y : BitVec 64) :
    x ||| (y &&& x) = x := by
  bv_decide

theorem and_or_absorb_comm_64 (x y : BitVec 64) :
    (x ||| y) &&& x = x := by
  bv_decide

theorem and_or_absorb_comm_right_64 (x y : BitVec 64) :
    (y ||| x) &&& x = x := by
  bv_decide

theorem or_and_absorb_comm_64 (x y : BitVec 64) :
    (x &&& y) ||| x = x := by
  bv_decide

theorem or_and_absorb_comm_right_64 (x y : BitVec 64) :
    (y &&& x) ||| x = x := by
  bv_decide

/-! ### Constant reassociation

    General replacements for the single `const_3_and_1_64` special case: the
    constants are universally quantified, so one theorem covers every pair. -/

theorem and_const_assoc_64 (x c1 c2 : BitVec 64) :
    (x &&& c1) &&& c2 = x &&& (c1 &&& c2) := by
  bv_decide

theorem or_const_assoc_64 (x c1 c2 : BitVec 64) :
    (x ||| c1) ||| c2 = x ||| (c1 ||| c2) := by
  bv_decide

theorem xor_const_assoc_64 (x c1 c2 : BitVec 64) :
    (x ^^^ c1) ^^^ c2 = x ^^^ (c1 ^^^ c2) := by
  bv_decide

theorem demorgan_not_and_64 (x y : BitVec 64) :
    ~~~(x &&& y) = (~~~x) ||| (~~~y) := by
  bv_decide

theorem demorgan_or_not_not_64 (x y : BitVec 64) :
    (~~~x) ||| (~~~y) = ~~~(x &&& y) := by
  bv_decide

theorem demorgan_not_and_not_not_64 (x y : BitVec 64) :
    ~~~((~~~x) &&& (~~~y)) = x ||| y := by
  bv_decide

theorem demorgan_not_or_64 (x y : BitVec 64) :
    ~~~(x ||| y) = (~~~x) &&& (~~~y) := by
  bv_decide

theorem demorgan_not_or_not_not_64 (x y : BitVec 64) :
    ~~~((~~~x) ||| (~~~y)) = x &&& y := by
  bv_decide

theorem shr_zero_64 (x : BitVec 64) :
    x >>> 0 = x := by
  bv_decide

end Cobra
