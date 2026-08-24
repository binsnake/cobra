import Cobra.Core

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

end Cobra
