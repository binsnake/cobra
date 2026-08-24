import Cobra.Core
import Cobra.Cert

/-! # Mixed-width expression semantics

The uniform model in `Cobra.Core` evaluates in a `BitVec width` carrier, so a
tree containing a cast or `Concat` cannot even be *stated* there. This module
adds the mixed-width world: `MExpr` mirrors the full Rust `Kind` (casts and
`Concat` included), and `evalW` mirrors the Rust compiled evaluator
(`crates/cobra-core/src/compiled.rs`) exactly — a fixed 64-bit carrier where

* constants and variables are masked at the *global* width `dw`,
* every same-width operator masks its result at its node-local width
  (the width of its first child, per `width_of`),
* casts mask/extend per `crates/cobra-core/src/arith.rs`.

Keeping this world in a separate type is deliberate: `Expr.SemEq` claims about
cast-bearing trees stay unrepresentable, so the uniform theorem pack cannot be
cited for a mixed tree by accident. Mixed claims use `MExpr.SemEqW`.
-/

namespace Cobra

/-- Low-`w` all-ones mask in the 64-bit carrier. Mirrors `arith::bitmask`:
`0` at width 0, `2^w - 1` for `1 ≤ w ≤ 63`, all-ones for `w ≥ 64`. -/
def maskBV (w : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ min w 64 - 1)

/-- Sign-bit mask at width `w`. Mirrors `arith::sign_bit_mask`. -/
def signBitBV (w : Nat) : BitVec 64 :=
  if w == 0 then 0#64 else BitVec.ofNat 64 (2 ^ (min w 64 - 1))

/-- Sign-extend a `src`-bit value to `dst` bits inside the 64-bit carrier.
Mirrors `arith::sext`, including the narrowing-degenerates-to-truncation
branch. -/
def sextBV (v : BitVec 64) (src dst : Nat) : BitVec 64 :=
  let low := v &&& maskBV src
  if src == 0 || dst ≤ src then
    low &&& maskBV dst
  else if low &&& signBitBV src ≠ 0#64 then
    (low ||| (maskBV dst &&& ~~~(maskBV src))) &&& maskBV dst
  else
    low &&& maskBV dst

/-- Mixed-width expression: the full Rust `Kind`, casts and `Concat`
included. -/
inductive MExpr where
  | const (value : Nat)
  | var (idx : Nat)
  | add (lhs rhs : MExpr)
  | mul (lhs rhs : MExpr)
  | band (lhs rhs : MExpr)
  | bor (lhs rhs : MExpr)
  | bxor (lhs rhs : MExpr)
  | bnot (arg : MExpr)
  | neg (arg : MExpr)
  | shr (arg : MExpr) (amount : Nat)
  | zext (arg : MExpr) (w : Nat)
  | sext (arg : MExpr) (w : Nat)
  | trunc (arg : MExpr) (w : Nat)
  | concat (hi lo : MExpr)
  deriving Repr, DecidableEq

namespace MExpr

/-- Result width of a node, mirroring `width_of`: leaves default to the
global width `dw`, same-width operators inherit their first child's width,
casts set it, `concat` sums. -/
def widthOf (dw : Nat) : MExpr -> Nat
  | const _ => dw
  | var _ => dw
  | add l _ => widthOf dw l
  | mul l _ => widthOf dw l
  | band l _ => widthOf dw l
  | bor l _ => widthOf dw l
  | bxor l _ => widthOf dw l
  | bnot a => widthOf dw a
  | neg a => widthOf dw a
  | shr a _ => widthOf dw a
  | zext _ w => w
  | sext _ w => w
  | trunc _ w => w
  | concat hi lo => widthOf dw hi + widthOf dw lo

/-- The Rust compiled evaluator, arm for arm. The carrier is always
`BitVec 64` (the Rust evaluator computes in `u64`); widths appear only as
masks. -/
def evalW (dw : Nat) (env : Nat -> BitVec 64) : MExpr -> BitVec 64
  | const value => BitVec.ofNat 64 value &&& maskBV dw
  | var idx => env idx &&& maskBV dw
  | add l r => (evalW dw env l + evalW dw env r) &&& maskBV (widthOf dw l)
  | mul l r => (evalW dw env l * evalW dw env r) &&& maskBV (widthOf dw l)
  | band l r => (evalW dw env l &&& evalW dw env r) &&& maskBV (widthOf dw l)
  | bor l r => (evalW dw env l ||| evalW dw env r) &&& maskBV (widthOf dw l)
  | bxor l r => (evalW dw env l ^^^ evalW dw env r) &&& maskBV (widthOf dw l)
  | bnot a => (~~~evalW dw env a) &&& maskBV (widthOf dw a)
  | neg a => (-evalW dw env a) &&& maskBV (widthOf dw a)
  | shr a amount => (evalW dw env a >>> amount) &&& maskBV (widthOf dw a)
  | zext a w => evalW dw env a &&& maskBV w
  | sext a w => sextBV (evalW dw env a) (widthOf dw a) w
  | trunc a w => evalW dw env a &&& maskBV w
  | concat hi lo =>
      ((evalW dw env hi <<< (widthOf dw lo % 64)) |||
          (evalW dw env lo &&& maskBV (widthOf dw lo))) &&&
        maskBV (widthOf dw hi + widthOf dw lo)

/-- Semantic equivalence at global width `dw` under the mixed evaluator. -/
def SemEqW (dw : Nat) (lhs rhs : MExpr) : Prop :=
  ∀ env : Nat -> BitVec 64, evalW dw env lhs = evalW dw env rhs

theorem SemEqW.refl (dw : Nat) (expr : MExpr) : SemEqW dw expr expr := by
  intro env
  rfl

theorem SemEqW.symm {dw : Nat} {lhs rhs : MExpr} :
    SemEqW dw lhs rhs -> SemEqW dw rhs lhs := by
  intro h env
  exact (h env).symm

theorem SemEqW.trans {dw : Nat} {a b c : MExpr} :
    SemEqW dw a b -> SemEqW dw b c -> SemEqW dw a c := by
  intro hab hbc env
  exact Eq.trans (hab env) (hbc env)

end MExpr

/-! ## Mask algebra -/

theorem and_mask_absorb (x m : BitVec 64) : x &&& m &&& m = x &&& m := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem getLsbD_maskBV (w i : Nat) :
    (maskBV w).getLsbD i = (decide (i < w) && decide (i < 64)) := by
  simp only [maskBV, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h64 : i < 64 <;> by_cases hw : i < w <;>
    simp [h64, hw, Nat.lt_min]

theorem maskBV_and_maskBV_of_le {w w' : Nat} (h : w ≤ w') :
    maskBV w &&& maskBV w' = maskBV w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, getLsbD_maskBV]
  by_cases hw : (i : Nat) < w
  · have : (i : Nat) < w' := Nat.lt_of_lt_of_le hw h
    simp [hw, this]
  · simp [hw]

namespace MExpr

theorem sextBV_masked (v : BitVec 64) (src dst : Nat) :
    sextBV v src dst &&& maskBV dst = sextBV v src dst := by
  simp only [sextBV]
  split
  · exact and_mask_absorb ..
  · split
    · exact and_mask_absorb ..
    · exact and_mask_absorb ..

/-- Every evaluated value is already masked at its own node width. This is the
invariant the cast theorems below lean on, and it holds arm by arm because
every `evalW` arm ends in a mask at the node's width. -/
theorem evalW_masked (dw : Nat) (env : Nat -> BitVec 64) (e : MExpr) :
    evalW dw env e &&& maskBV (widthOf dw e) = evalW dw env e := by
  cases e <;> simp only [evalW, widthOf] <;>
    first
      | exact and_mask_absorb ..
      | exact sextBV_masked ..

/-- A value masked at `u` is untouched by any wider mask. -/
theorem masked_and_wider {v : BitVec 64} {u w : Nat}
    (hv : v &&& maskBV u = v) (h : u ≤ w) : v &&& maskBV w = v := by
  rw [<- hv, BitVec.and_assoc, maskBV_and_maskBV_of_le h]

/-! ## Cast rewrite theorems

Each is width-generic; the Rust recognizer checks the width side conditions
structurally (widths are concrete at certificate time). All four preserve the
node width, which `MCtx.plug_preserves_sem_eq_w` requires. -/

/-- `zext e w = e` when `e` is already `w` wide. -/
theorem zext_identity {dw : Nat} {e : MExpr} {w : Nat}
    (hw : e.widthOf dw = w) : SemEqW dw (MExpr.zext e w) e := by
  intro env
  simp only [evalW]
  rw [<- hw]
  exact evalW_masked ..

/-- `trunc e w = e` when `e` is already `w` wide. -/
theorem trunc_identity {dw : Nat} {e : MExpr} {w : Nat}
    (hw : e.widthOf dw = w) : SemEqW dw (MExpr.trunc e w) e := by
  intro env
  simp only [evalW]
  rw [<- hw]
  exact evalW_masked ..

/-- `sext e w = e` when `e` is already `w` wide: the source and target widths
coincide, so the extension region is empty. -/
theorem sext_identity {dw : Nat} {e : MExpr} {w : Nat}
    (hw : e.widthOf dw = w) : SemEqW dw (MExpr.sext e w) e := by
  intro env
  simp only [evalW, sextBV, hw]
  have hcond : (w == 0 || decide (w ≤ w)) = true := by
    simp
  rw [if_pos hcond, and_mask_absorb, <- hw]
  exact evalW_masked ..

/-- Widening `zext` composition collapses: `zext (zext e w1) w2 = zext e w2`
when the inner extension is genuinely widening. -/
theorem zext_zext {dw : Nat} {e : MExpr} {w1 w2 : Nat}
    (h : e.widthOf dw ≤ w1) :
    SemEqW dw (MExpr.zext (MExpr.zext e w1) w2) (MExpr.zext e w2) := by
  intro env
  simp only [evalW]
  rw [masked_and_wider (evalW_masked dw env e) h]

/-- `trunc` composition collapses: `trunc (trunc e w1) w2 = trunc e w2` when
the outer truncation is at most as wide. -/
theorem trunc_trunc {dw : Nat} {e : MExpr} {w1 w2 : Nat}
    (h : w2 ≤ w1) :
    SemEqW dw (MExpr.trunc (MExpr.trunc e w1) w2) (MExpr.trunc e w2) := by
  intro env
  simp only [evalW]
  rw [BitVec.and_assoc, BitVec.and_comm (maskBV w1), maskBV_and_maskBV_of_le h]

/-- Round trip: widening `zext` followed by `trunc` back to the source width
is the identity. -/
theorem trunc_zext {dw : Nat} {e : MExpr} {w1 w2 : Nat}
    (h1 : e.widthOf dw ≤ w1) (h2 : e.widthOf dw = w2) :
    SemEqW dw (MExpr.trunc (MExpr.zext e w1) w2) e := by
  intro env
  simp only [evalW]
  rw [masked_and_wider (evalW_masked dw env e) h1, <- h2]
  exact evalW_masked ..

end MExpr

/-! ## Contexts over mixed trees -/

/-- One-hole context over `MExpr`, cast and `concat` frames included. -/
inductive MCtx where
  | hole
  | addL (ctx : MCtx) (rhs : MExpr)
  | addR (lhs : MExpr) (ctx : MCtx)
  | mulL (ctx : MCtx) (rhs : MExpr)
  | mulR (lhs : MExpr) (ctx : MCtx)
  | bandL (ctx : MCtx) (rhs : MExpr)
  | bandR (lhs : MExpr) (ctx : MCtx)
  | borL (ctx : MCtx) (rhs : MExpr)
  | borR (lhs : MExpr) (ctx : MCtx)
  | bxorL (ctx : MCtx) (rhs : MExpr)
  | bxorR (lhs : MExpr) (ctx : MCtx)
  | bnot (ctx : MCtx)
  | neg (ctx : MCtx)
  | shr (ctx : MCtx) (amount : Nat)
  | zext (ctx : MCtx) (w : Nat)
  | sext (ctx : MCtx) (w : Nat)
  | trunc (ctx : MCtx) (w : Nat)
  | concatHi (ctx : MCtx) (lo : MExpr)
  | concatLo (hi : MExpr) (ctx : MCtx)
  deriving Repr, DecidableEq

namespace MCtx

def plug : MCtx -> MExpr -> MExpr
  | hole, expr => expr
  | addL ctx rhs, expr => MExpr.add (plug ctx expr) rhs
  | addR lhs ctx, expr => MExpr.add lhs (plug ctx expr)
  | mulL ctx rhs, expr => MExpr.mul (plug ctx expr) rhs
  | mulR lhs ctx, expr => MExpr.mul lhs (plug ctx expr)
  | bandL ctx rhs, expr => MExpr.band (plug ctx expr) rhs
  | bandR lhs ctx, expr => MExpr.band lhs (plug ctx expr)
  | borL ctx rhs, expr => MExpr.bor (plug ctx expr) rhs
  | borR lhs ctx, expr => MExpr.bor lhs (plug ctx expr)
  | bxorL ctx rhs, expr => MExpr.bxor (plug ctx expr) rhs
  | bxorR lhs ctx, expr => MExpr.bxor lhs (plug ctx expr)
  | bnot ctx, expr => MExpr.bnot (plug ctx expr)
  | neg ctx, expr => MExpr.neg (plug ctx expr)
  | shr ctx amount, expr => MExpr.shr (plug ctx expr) amount
  | zext ctx w, expr => MExpr.zext (plug ctx expr) w
  | sext ctx w, expr => MExpr.sext (plug ctx expr) w
  | trunc ctx w, expr => MExpr.trunc (plug ctx expr) w
  | concatHi ctx lo, expr => MExpr.concat (plug ctx expr) lo
  | concatLo hi ctx, expr => MExpr.concat hi (plug ctx expr)

/-- Width-preserving rewrites keep the width of any surrounding tree. -/
theorem widthOf_plug_congr {dw : Nat} (ctx : MCtx) {b a : MExpr}
    (hw : b.widthOf dw = a.widthOf dw) :
    (plug ctx b).widthOf dw = (plug ctx a).widthOf dw := by
  induction ctx <;> simp [plug, MExpr.widthOf, *]

/-- Plugging a width-preserving semantic equivalence into any context
preserves mixed-width semantic equivalence.

The width-preservation hypothesis is load-bearing: same-width operators in the
context mask at the width of their (possibly plugged) first child, so a
rewrite that changed the hole's width would change every enclosing mask. -/
theorem plug_preserves_sem_eq_w {dw : Nat} (ctx : MCtx) {b a : MExpr}
    (hw : b.widthOf dw = a.widthOf dw)
    (h : MExpr.SemEqW dw b a) :
    MExpr.SemEqW dw (plug ctx b) (plug ctx a) := by
  intro env
  induction ctx with
  | hole => exact h env
  | addL ctx rhs ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | addR lhs ctx ih => simp [plug, MExpr.evalW, ih]
  | mulL ctx rhs ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | mulR lhs ctx ih => simp [plug, MExpr.evalW, ih]
  | bandL ctx rhs ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | bandR lhs ctx ih => simp [plug, MExpr.evalW, ih]
  | borL ctx rhs ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | borR lhs ctx ih => simp [plug, MExpr.evalW, ih]
  | bxorL ctx rhs ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | bxorR lhs ctx ih => simp [plug, MExpr.evalW, ih]
  | bnot ctx ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | neg ctx ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | shr ctx amount ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | zext ctx w ih => simp [plug, MExpr.evalW, ih]
  | sext ctx w ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | trunc ctx w ih => simp [plug, MExpr.evalW, ih]
  | concatHi ctx lo ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]
  | concatLo hi ctx ih => simp [plug, MExpr.evalW, ih, widthOf_plug_congr ctx hw]

end MCtx

/-! ## Step and chain soundness, mixed world -/

structure RewriteStepW where
  ctx : MCtx
  before : MExpr
  after : MExpr

namespace RewriteStepW

def source (step : RewriteStepW) : MExpr :=
  step.ctx.plug step.before

def target (step : RewriteStepW) : MExpr :=
  step.ctx.plug step.after

theorem sound {dw : Nat} (step : RewriteStepW)
    (hw : step.before.widthOf dw = step.after.widthOf dw) :
    MExpr.SemEqW dw step.before step.after ->
    MExpr.SemEqW dw step.source step.target := by
  exact MCtx.plug_preserves_sem_eq_w step.ctx hw

end RewriteStepW

inductive ChainW (dw : Nat) : MExpr -> MExpr -> Prop where
  | done (expr : MExpr) : ChainW dw expr expr
  | step {a b c : MExpr} :
      MExpr.SemEqW dw a b ->
      ChainW dw b c ->
      ChainW dw a c

namespace ChainW

theorem sound {dw : Nat} {lhs rhs : MExpr} :
    ChainW dw lhs rhs -> MExpr.SemEqW dw lhs rhs := by
  intro chain
  induction chain with
  | done expr => exact MExpr.SemEqW.refl dw expr
  | step h _ ih => exact MExpr.SemEqW.trans h ih

end ChainW

/-! ## Bridge: the uniform world embeds into the mixed world

`ofExpr` maps a uniform expression into `MExpr`; its image is cast-free by
construction. `evalW_ofExpr` is the carry bridge: evaluating the image in the
64-bit masked carrier equals zero-extending the native `BitVec dw` evaluation.
The arithmetic cases are where the carry reasoning lives — an addition
computed in the wide carrier and masked afterwards agrees with the addition
computed natively at width `dw` because `2 ^ dw ∣ 2 ^ 64` collapses the double
reduction, and negation needs `(2 ^ 64 - a) ≡ (2 ^ dw - a) [MOD 2 ^ dw]`.
`semEqW_of_semEq` then lifts every theorem of the uniform pack into the mixed
world, which is what lets a mixed-chain step on a cast-free redex cite the
named theorem instead of a decision procedure. -/

def ofExpr : Expr -> MExpr
  | .const value => .const value
  | .var idx => .var idx
  | .add lhs rhs => .add (ofExpr lhs) (ofExpr rhs)
  | .mul lhs rhs => .mul (ofExpr lhs) (ofExpr rhs)
  | .band lhs rhs => .band (ofExpr lhs) (ofExpr rhs)
  | .bor lhs rhs => .bor (ofExpr lhs) (ofExpr rhs)
  | .bxor lhs rhs => .bxor (ofExpr lhs) (ofExpr rhs)
  | .bnot arg => .bnot (ofExpr arg)
  | .neg arg => .neg (ofExpr arg)
  | .shr arg amount => .shr (ofExpr arg) amount

theorem widthOf_ofExpr (dw : Nat) (e : Expr) : (ofExpr e).widthOf dw = dw := by
  induction e <;> simp [ofExpr, MExpr.widthOf, *]

theorem maskBV_toNat {dw : Nat} (h : dw ≤ 64) : (maskBV dw).toNat = 2 ^ dw - 1 := by
  have hpow : (2 : Nat) ^ dw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
  simp only [maskBV, Nat.min_eq_left h, BitVec.toNat_ofNat]
  omega

theorem toNat_and_maskBV {dw : Nat} (h : dw ≤ 64) (x : BitVec 64) :
    (x &&& maskBV dw).toNat = x.toNat % 2 ^ dw := by
  rw [BitVec.toNat_and, maskBV_toNat h, Nat.and_two_pow_sub_one_eq_mod]

/-- Masking at `dw` in the carrier is exactly truncate-then-widen. -/
theorem and_maskBV_eq_setWidth {dw : Nat} (h : dw ≤ 64) (x : BitVec 64) :
    x &&& maskBV dw = BitVec.setWidth 64 (BitVec.setWidth dw x) := by
  have hpow : (2 : Nat) ^ dw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
  have hlt : x.toNat % 2 ^ dw < 2 ^ dw := Nat.mod_lt _ (Nat.two_pow_pos dw)
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_maskBV h, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- Truncating a widened value back to its own width is the identity. -/
theorem setWidth_setWidth_self {dw : Nat} (h : dw ≤ 64) (a : BitVec dw) :
    BitVec.setWidth dw (BitVec.setWidth 64 a) = a := by
  rw [BitVec.setWidth_setWidth (by omega), BitVec.setWidth_eq]

theorem add_transport {dw : Nat} (h : dw ≤ 64) (a b : BitVec dw) :
    (BitVec.setWidth 64 a + BitVec.setWidth 64 b) &&& maskBV dw =
      BitVec.setWidth 64 (a + b) := by
  rw [and_maskBV_eq_setWidth h, BitVec.setWidth_add _ _ h, setWidth_setWidth_self h,
    setWidth_setWidth_self h]

theorem mul_transport {dw : Nat} (h : dw ≤ 64) (a b : BitVec dw) :
    (BitVec.setWidth 64 a * BitVec.setWidth 64 b) &&& maskBV dw =
      BitVec.setWidth 64 (a * b) := by
  rw [and_maskBV_eq_setWidth h, BitVec.setWidth_mul _ _ h, setWidth_setWidth_self h,
    setWidth_setWidth_self h]

/-- The negation carry lemma: subtracting from either modulus agrees below the
smaller one. -/
theorem sub_pow_mod {d bigD a : Nat} (hdvd : d ∣ bigD) (hd : 0 < d) (hD : d ≤ bigD)
    (ha : a < d) : (bigD - a) % d = (d - a) % d := by
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hD
      omega
    · exact hpos
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · simp [Nat.mul_mod_right, Nat.mod_self]
  · have hdk : d ≤ d * k := Nat.le_mul_of_pos_right d hk1
    have hmul : d * (k - 1) = d * k - d := by
      rw [Nat.mul_sub, Nat.mul_one]
    have hsplit : d * k - a = d * (k - 1) + (d - a) := by omega
    rw [hsplit, Nat.mul_add_mod]

theorem neg_transport {dw : Nat} (h : dw ≤ 64) (a : BitVec dw) :
    (-BitVec.setWidth 64 a) &&& maskBV dw = BitVec.setWidth 64 (-a) := by
  have hpow : (2 : Nat) ^ dw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
  have hdvd : (2 : Nat) ^ dw ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 h
  have ha : a.toNat < 2 ^ dw := a.isLt
  have hd : (0 : Nat) < 2 ^ dw := Nat.two_pow_pos dw
  apply BitVec.eq_of_toNat_eq
  have hL : ((-BitVec.setWidth 64 a) &&& maskBV dw).toNat =
      (2 ^ dw - a.toNat) % 2 ^ dw := by
    rw [toNat_and_maskBV h, BitVec.toNat_neg, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega), Nat.mod_mod_of_dvd _ hdvd,
      sub_pow_mod hdvd hd hpow ha]
  have hR : (BitVec.setWidth 64 (-a)).toNat = (2 ^ dw - a.toNat) % 2 ^ dw := by
    have hmlt : (2 ^ dw - a.toNat) % 2 ^ dw < 2 ^ dw := Nat.mod_lt _ hd
    rw [BitVec.toNat_setWidth, BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
  rw [hL, hR]

theorem and_transport {dw : Nat} (a b : BitVec dw) :
    (BitVec.setWidth 64 a &&& BitVec.setWidth 64 b) &&& maskBV dw =
      BitVec.setWidth 64 (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, getLsbD_maskBV, BitVec.getLsbD_setWidth]
  by_cases hdw : i < dw
  · simp [hdw, hi]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (Nat.le_of_not_lt hdw)
    have hfb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (Nat.le_of_not_lt hdw)
    simp [hdw, hfa, hfb]

theorem or_transport {dw : Nat} (a b : BitVec dw) :
    (BitVec.setWidth 64 a ||| BitVec.setWidth 64 b) &&& maskBV dw =
      BitVec.setWidth 64 (a ||| b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, getLsbD_maskBV, BitVec.getLsbD_setWidth]
  by_cases hdw : i < dw
  · simp [hdw, hi]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (Nat.le_of_not_lt hdw)
    have hfb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (Nat.le_of_not_lt hdw)
    simp [hdw, hfa, hfb]

theorem xor_transport {dw : Nat} (a b : BitVec dw) :
    (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b) &&& maskBV dw =
      BitVec.setWidth 64 (a ^^^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, getLsbD_maskBV, BitVec.getLsbD_setWidth]
  by_cases hdw : i < dw
  · simp [hdw, hi]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (Nat.le_of_not_lt hdw)
    have hfb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (Nat.le_of_not_lt hdw)
    simp [hdw, hfa, hfb]

theorem not_transport {dw : Nat} (a : BitVec dw) :
    (~~~BitVec.setWidth 64 a) &&& maskBV dw = BitVec.setWidth 64 (~~~a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_maskBV, BitVec.getLsbD_setWidth]
  by_cases hdw : i < dw
  · simp [hdw, hi]
  · simp [hdw, hi]

theorem shr_transport {dw : Nat} (h : dw ≤ 64) (a : BitVec dw) (k : Nat) :
    (BitVec.setWidth 64 a >>> k) &&& maskBV dw = BitVec.setWidth 64 (a >>> k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_maskBV,
    BitVec.getLsbD_setWidth]
  by_cases hdw : i < dw
  · by_cases hk : k + i < 64
    · simp [hdw, hi, hk]
    · have hfalse : a.getLsbD (k + i) = false :=
        BitVec.getLsbD_of_ge a (k + i) (by omega)
      simp [hdw, hi, hk, hfalse]
  · have hfalse : a.getLsbD (k + i) = false :=
      BitVec.getLsbD_of_ge a (k + i) (by omega)
    simp [hdw, hfalse]

/-- Truncate a 64-bit environment to width `dw`. -/
def envTrunc (dw : Nat) (env : Nat -> BitVec 64) : Nat -> BitVec dw :=
  fun idx => BitVec.setWidth dw (env idx)

/-- The carry bridge: evaluating a uniform expression's image in the 64-bit
masked carrier is the zero-extension of its native `BitVec dw` evaluation. -/
theorem evalW_ofExpr {dw : Nat} (h : dw ≤ 64) (env : Nat -> BitVec 64) (e : Expr) :
    MExpr.evalW dw env (ofExpr e) =
      BitVec.setWidth 64 (Expr.eval dw (envTrunc dw env) e) := by
  induction e with
  | const value =>
      have hpow : (2 : Nat) ^ dw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
      have hdvd : (2 : Nat) ^ dw ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 h
      have hlt : value % 2 ^ dw < 2 ^ dw := Nat.mod_lt _ (Nat.two_pow_pos dw)
      simp only [ofExpr, MExpr.evalW, Expr.eval]
      apply BitVec.eq_of_toNat_eq
      have hL : (BitVec.ofNat 64 value &&& maskBV dw).toNat = value % 2 ^ dw := by
        rw [toNat_and_maskBV h, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd]
      have hR : (BitVec.setWidth 64 (BitVec.ofNat dw value)).toNat = value % 2 ^ dw := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hL, hR]
  | var idx =>
      simpa [ofExpr, MExpr.evalW, Expr.eval, envTrunc] using
        and_maskBV_eq_setWidth h (env idx)
  | add lhs rhs ihl ihr =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ihl, ihr, add_transport h]
  | mul lhs rhs ihl ihr =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ihl, ihr, mul_transport h]
  | band lhs rhs ihl ihr =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ihl, ihr, and_transport]
  | bor lhs rhs ihl ihr =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ihl, ihr, or_transport]
  | bxor lhs rhs ihl ihr =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ihl, ihr, xor_transport]
  | bnot arg ih =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ih, not_transport]
  | neg arg ih =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ih, neg_transport h]
  | shr arg amount ih =>
      simp [ofExpr, MExpr.evalW, Expr.eval, widthOf_ofExpr, ih, shr_transport h]

/-- Lift a uniform-pack equivalence into the mixed world. This is what lets a
mixed-chain step on a cast-free redex cite the named uniform theorem. -/
theorem semEqW_of_semEq {dw : Nat} (h : dw ≤ 64) {a b : Expr}
    (hab : Expr.SemEq dw a b) :
    MExpr.SemEqW dw (ofExpr a) (ofExpr b) := by
  intro env
  rw [evalW_ofExpr h, evalW_ofExpr h, hab (envTrunc dw env)]

end Cobra
