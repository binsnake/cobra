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

/-! ### The carry identity

`bv_decide` needs a concrete width, so the arithmetic MBA identities cannot be
decided width-generically. They are instead derived from one fundamental carry
fact — `(a &&& b) + (a ||| b) = a + b` — proved at the `Nat` level by
induction on binary digits, then lifted through `toNat`. Everything else in
the width-generic arithmetic pack below is equational consequence. -/

/-- Bit-level carry balance: at the lowest bit, `and` plus `or` carries the
same total as the two addends. -/
theorem nat_and_or_mod_two (a b : Nat) :
    (a &&& b) % 2 + (a ||| b) % 2 = a % 2 + b % 2 := by
  have hand := Nat.testBit_and a b 0
  have hor := Nat.testBit_or a b 0
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
      rcases Nat.mod_two_eq_zero_or_one (a &&& b) with h3 | h3 <;>
        rcases Nat.mod_two_eq_zero_or_one (a ||| b) with h4 | h4 <;>
          simp [Nat.testBit_zero, h1, h2, h3, h4] at hand hor ⊢

/-- The fundamental carry identity: `and` collects the carries, `or` the
digit sums, and together they account for full addition. -/
theorem nat_and_add_or (a b : Nat) : (a &&& b) + (a ||| b) = a + b := by
  induction a using Nat.div2Induction generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha
      simp [Nat.zero_and, Nat.zero_or]
    · have ihb := ih (Nat.pos_of_ne_zero ha) (b / 2)
      have hda := Nat.div_add_mod a 2
      have hdb := Nat.div_add_mod b 2
      have hdand := Nat.div_add_mod (a &&& b) 2
      have hdor := Nat.div_add_mod (a ||| b) 2
      rw [Nat.and_div_two] at hdand
      rw [Nat.or_div_two] at hdor
      have hbit := nat_and_or_mod_two a b
      omega

theorem and_or_sum_eq_add_w {w : Nat} (x y : BitVec w) :
    (x &&& y) + (x ||| y) = x + y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_or, nat_and_add_or]

/-- Disjoint bit-vectors add without carries. -/
theorem add_eq_or_of_and_eq_zero_w {w : Nat} {x y : BitVec w} (h : x &&& y = 0#w) :
    x + y = x ||| y := by
  have hsum := and_or_sum_eq_add_w x y
  rw [h, BitVec.zero_add] at hsum
  exact hsum.symm

set_option linter.unusedSimpArgs false in
theorem and_xor_disjoint_w {w : Nat} (x y : BitVec w) :
    (x &&& y) &&& (x ^^^ y) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp [hx, hy]

set_option linter.unusedSimpArgs false in
theorem and_or_xor_cover_w {w : Nat} (x y : BitVec w) :
    (x &&& y) ||| (x ^^^ y) = x ||| y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp [hx, hy]

/-- `xor` and doubled `and` split a sum: the digit part and the carry part. -/
theorem and_add_xor_w {w : Nat} (x y : BitVec w) :
    (x &&& y) + (x ^^^ y) = x ||| y := by
  rw [add_eq_or_of_and_eq_zero_w (and_xor_disjoint_w x y), and_or_xor_cover_w]

set_option linter.unusedSimpArgs false in
theorem not_and_and_disjoint_w {w : Nat} (x y : BitVec w) :
    (~~~x) &&& (x &&& y) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
  cases hx : x.getLsbD i <;> simp [hx, hi]

set_option linter.unusedSimpArgs false in
theorem not_or_and_cover_w {w : Nat} (x y : BitVec w) :
    (~~~x) ||| (x &&& y) = (~~~x) ||| y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not]
  cases hx : x.getLsbD i <;> simp [hx, hi]

/-- Splitting `~~~x ||| y` as a carry-free sum. -/
theorem not_or_split_w {w : Nat} (x y : BitVec w) :
    (~~~x) ||| y = ~~~x + (x &&& y) := by
  rw [add_eq_or_of_and_eq_zero_w (not_and_and_disjoint_w x y), not_or_and_cover_w]

/-- `x + -x = 0`, spelled through subtraction. -/
theorem add_neg_self_w {w : Nat} (x : BitVec w) : x + -x = 0#w := by
  rw [← BitVec.sub_eq_add_neg, BitVec.sub_self]

theorem neg_add_self_w {w : Nat} (x : BitVec w) : -x + x = 0#w := by
  rw [BitVec.add_comm]
  exact add_neg_self_w x

/-! ### Arithmetic MBA identities, width-generic

The statements mirror the `_64` pack exactly (same argument shapes, `64`
replaced by `w`), so a certificate citing the `_64` name at width 64 can cite
the `_w` name at any other width with the same instance arguments. Each proof
is an equational consequence of the carry identity above — no decision
procedure is involved, which is what makes them width-generic. -/

theorem bnot_eq_neg_add_mask_w {w : Nat} (x : BitVec w) :
    ~~~x = -x - 1#w := by
  rw [BitVec.neg_eq_not_add, BitVec.add_sub_cancel]

/-- Cobra's `allOnes` (defined as `~~~0`) is the library's `BitVec.allOnes`. -/
theorem cobra_allOnes_eq (w : Nat) : allOnes w = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [allOnes, hi]

theorem bnot_eq_neg_add_all_ones_w {w : Nat} (x : BitVec w) :
    ~~~x = -x + allOnes w := by
  rw [bnot_eq_neg_add_mask_w x, BitVec.sub_eq_add_neg, cobra_allOnes_eq,
    ← BitVec.neg_one_eq_allOnes]

theorem xor_add_two_mul_and_eq_add_w {w : Nat} (x y : BitVec w) :
    (x ^^^ y) + (2#w * (x &&& y)) = x + y := by
  rw [BitVec.two_mul]
  calc (x ^^^ y) + ((x &&& y) + (x &&& y))
      = (x &&& y) + ((x &&& y) + (x ^^^ y)) := by ac_rfl
    _ = (x &&& y) + (x ||| y) := by rw [and_add_xor_w]
    _ = x + y := and_or_sum_eq_add_w x y

theorem xor_eq_add_sub_two_mul_and_w {w : Nat} (x y : BitVec w) :
    x ^^^ y = x + y - (2#w * (x &&& y)) := by
  rw [← xor_add_two_mul_and_eq_add_w x y, BitVec.add_sub_cancel]

theorem or_sub_and_eq_xor_w {w : Nat} (x y : BitVec w) :
    (x ||| y) - (x &&& y) = x ^^^ y := by
  rw [← and_add_xor_w, BitVec.add_comm, BitVec.add_sub_cancel]

theorem two_mul_and_or_sum_eq_two_mul_add_w {w : Nat} (x y : BitVec w) :
    (2#w * (x &&& y)) + (2#w * (x ||| y)) = (2#w * x) + (2#w * y) := by
  rw [BitVec.two_mul, BitVec.two_mul, BitVec.two_mul, BitVec.two_mul]
  calc (x &&& y) + (x &&& y) + ((x ||| y) + (x ||| y))
      = ((x &&& y) + (x ||| y)) + ((x &&& y) + (x ||| y)) := by ac_rfl
    _ = (x + y) + (x + y) := by rw [and_or_sum_eq_add_w]
    _ = x + x + (y + y) := by ac_rfl

theorem not_or_sub_not_eq_and_w {w : Nat} (x y : BitVec w) :
    ((~~~x) ||| y) - (~~~x) = x &&& y := by
  rw [not_or_split_w, BitVec.add_comm, BitVec.add_sub_cancel]

theorem not_or_add_self_add_one_eq_and_w {w : Nat} (x y : BitVec w) :
    ((~~~x) ||| y) + x + 1#w = x &&& y := by
  rw [not_or_split_w]
  calc (~~~x + (x &&& y)) + x + 1#w
      = (x &&& y) + ((~~~x + 1#w) + x) := by ac_rfl
    _ = (x &&& y) + (-x + x) := by rw [BitVec.neg_eq_not_add]
    _ = (x &&& y) + 0#w := by rw [neg_add_self_w]
    _ = x &&& y := BitVec.add_zero _

theorem xor_via_or_not_w {w : Nat} (x y : BitVec w) :
    x - y - (2#w * (x ||| (~~~y))) - 2#w = x ^^^ y := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.sub_eq_iff_eq_add, BitVec.sub_eq_iff_eq_add]
  symm
  have hsplit : x ||| ~~~y = ~~~y + (x &&& y) := by
    rw [BitVec.or_comm, not_or_split_w, BitVec.and_comm]
  have htwo : (2#w : BitVec w) = 1#w + 1#w := (BitVec.ofNat_add_ofNat 1 1).symm
  calc (x ^^^ y) + 2#w + 2#w * (x ||| ~~~y) + y
      = (x ^^^ y) + (1#w + 1#w) + ((~~~y + (x &&& y)) + (~~~y + (x &&& y))) + y := by
        rw [BitVec.two_mul, hsplit, ← htwo]
    _ = ((x ^^^ y) + ((x &&& y) + (x &&& y))) + ((~~~y + 1#w) + ((~~~y + 1#w) + y)) := by
        ac_rfl
    _ = (x + y) + (-y + (-y + y)) := by
        rw [← BitVec.two_mul, xor_add_two_mul_and_eq_add_w, ← BitVec.neg_eq_not_add]
    _ = (x + y) + (-y + 0#w) := by rw [neg_add_self_w]
    _ = (x + y) + -y := by rw [BitVec.add_zero]
    _ = (x + y) - y := by rw [BitVec.sub_eq_add_neg]
    _ = x := BitVec.add_sub_cancel x y

set_option linter.unusedSimpArgs false in
theorem xor_and_eq_and_not_w {w : Nat} (x y : BitVec w) :
    x ^^^ (x &&& y) = x &&& (~~~y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp [hx, hy, hi]

theorem const_3_and_1_w {w : Nat} : 3#w &&& 1#w = 1#w := by
  match w with
  | 0 => decide
  | 1 => decide
  | w + 2 =>
    have h4 : (4 : Nat) ≤ 2 ^ (w + 2) := by
      have : (2 : Nat) ^ 2 ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    decide

theorem add_comm_w {w : Nat} (x y : BitVec w) : x + y = y + x :=
  BitVec.add_comm x y

theorem add_assoc_w {w : Nat} (x y z : BitVec w) : (x + y) + z = x + (y + z) :=
  BitVec.add_assoc x y z

theorem mul_comm_w {w : Nat} (x y : BitVec w) : x * y = y * x :=
  BitVec.mul_comm x y

theorem mul_assoc_w {w : Nat} (x y z : BitVec w) : (x * y) * z = x * (y * z) :=
  BitVec.mul_assoc x y z

theorem mul_add_w {w : Nat} (x y z : BitVec w) : x * (y + z) = x * y + x * z :=
  BitVec.mul_add

theorem add_mul_w {w : Nat} (x y z : BitVec w) : (x + y) * z = x * z + y * z := by
  rw [BitVec.mul_comm, BitVec.mul_add, BitVec.mul_comm z x, BitVec.mul_comm z y]

/-! ## Width-parametric pack

    The theorems below are the width-generic counterparts of the `_64` pack's
    remaining identities: pure bitwise and ring facts that hold at every width
    directly. Together with the carry-derived arithmetic pack above, every
    recognized rewrite now has a width-generic counterpart, so the certificate
    machinery can cite the full pack at any bitwidth. -/

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
  cases hx : x.getLsbD i <;> simp [h]

theorem not_xor_self_w {w : Nat} (x : BitVec w) : (~~~x) ^^^ x = allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [allOnes]
  intro h
  cases hx : x.getLsbD i <;> simp [h]

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
