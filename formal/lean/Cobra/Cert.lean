import Cobra.Core

namespace Cobra

namespace Expr

def SemEq (width : Nat) (lhs rhs : Expr) : Prop :=
  ∀ env : Nat -> BitVec width, Expr.eval width env lhs = Expr.eval width env rhs

theorem SemEq.refl (width : Nat) (expr : Expr) :
    SemEq width expr expr := by
  intro env
  rfl

theorem SemEq.symm {width : Nat} {lhs rhs : Expr} :
    SemEq width lhs rhs -> SemEq width rhs lhs := by
  intro h env
  exact (h env).symm

theorem SemEq.trans {width : Nat} {a b c : Expr} :
    SemEq width a b -> SemEq width b c -> SemEq width a c := by
  intro hab hbc env
  exact Eq.trans (hab env) (hbc env)

end Expr

inductive Ctx where
  | hole
  | addL (ctx : Ctx) (rhs : Expr)
  | addR (lhs : Expr) (ctx : Ctx)
  | mulL (ctx : Ctx) (rhs : Expr)
  | mulR (lhs : Expr) (ctx : Ctx)
  | bandL (ctx : Ctx) (rhs : Expr)
  | bandR (lhs : Expr) (ctx : Ctx)
  | borL (ctx : Ctx) (rhs : Expr)
  | borR (lhs : Expr) (ctx : Ctx)
  | bxorL (ctx : Ctx) (rhs : Expr)
  | bxorR (lhs : Expr) (ctx : Ctx)
  | bnot (ctx : Ctx)
  | neg (ctx : Ctx)
  | shr (ctx : Ctx) (amount : Nat)
  deriving Repr, DecidableEq

namespace Ctx

def plug : Ctx -> Expr -> Expr
  | hole, expr => expr
  | addL ctx rhs, expr => Expr.add (plug ctx expr) rhs
  | addR lhs ctx, expr => Expr.add lhs (plug ctx expr)
  | mulL ctx rhs, expr => Expr.mul (plug ctx expr) rhs
  | mulR lhs ctx, expr => Expr.mul lhs (plug ctx expr)
  | bandL ctx rhs, expr => Expr.band (plug ctx expr) rhs
  | bandR lhs ctx, expr => Expr.band lhs (plug ctx expr)
  | borL ctx rhs, expr => Expr.bor (plug ctx expr) rhs
  | borR lhs ctx, expr => Expr.bor lhs (plug ctx expr)
  | bxorL ctx rhs, expr => Expr.bxor (plug ctx expr) rhs
  | bxorR lhs ctx, expr => Expr.bxor lhs (plug ctx expr)
  | bnot ctx, expr => Expr.bnot (plug ctx expr)
  | neg ctx, expr => Expr.neg (plug ctx expr)
  | shr ctx amount, expr => Expr.shr (plug ctx expr) amount

theorem plug_preserves_sem_eq {width : Nat} (ctx : Ctx) {before after : Expr} :
    Expr.SemEq width before after ->
    Expr.SemEq width (plug ctx before) (plug ctx after) := by
  intro h env
  induction ctx with
  | hole =>
      exact h env
  | addL ctx rhs ih =>
      simp [plug, Expr.eval, ih]
  | addR lhs ctx ih =>
      simp [plug, Expr.eval, ih]
  | mulL ctx rhs ih =>
      simp [plug, Expr.eval, ih]
  | mulR lhs ctx ih =>
      simp [plug, Expr.eval, ih]
  | bandL ctx rhs ih =>
      simp [plug, Expr.eval, ih]
  | bandR lhs ctx ih =>
      simp [plug, Expr.eval, ih]
  | borL ctx rhs ih =>
      simp [plug, Expr.eval, ih]
  | borR lhs ctx ih =>
      simp [plug, Expr.eval, ih]
  | bxorL ctx rhs ih =>
      simp [plug, Expr.eval, ih]
  | bxorR lhs ctx ih =>
      simp [plug, Expr.eval, ih]
  | bnot ctx ih =>
      simp [plug, Expr.eval, ih]
  | neg ctx ih =>
      simp [plug, Expr.eval, ih]
  | shr ctx amount ih =>
      simp [plug, Expr.eval, ih]

end Ctx

structure RewriteStep where
  ctx : Ctx
  before : Expr
  after : Expr

namespace RewriteStep

def source (step : RewriteStep) : Expr :=
  step.ctx.plug step.before

def target (step : RewriteStep) : Expr :=
  step.ctx.plug step.after

theorem sound {width : Nat} (step : RewriteStep) :
    Expr.SemEq width step.before step.after ->
    Expr.SemEq width step.source step.target := by
  exact Ctx.plug_preserves_sem_eq step.ctx

end RewriteStep

inductive Chain (width : Nat) : Expr -> Expr -> Prop where
  | done (expr : Expr) : Chain width expr expr
  | step {a b c : Expr} :
      Expr.SemEq width a b ->
      Chain width b c ->
      Chain width a c

namespace Chain

theorem sound {width : Nat} {lhs rhs : Expr} :
    Chain width lhs rhs -> Expr.SemEq width lhs rhs := by
  intro chain
  induction chain with
  | done expr =>
      exact Expr.SemEq.refl width expr
  | step h _ ih =>
      exact Expr.SemEq.trans h ih

end Chain

end Cobra
