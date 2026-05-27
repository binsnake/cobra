import Cobra.Core

namespace Cobra

def boolEnv (width : Nat) (assignment : Nat) : Nat -> BitVec width :=
  fun idx => BitVec.ofNat width ((assignment / (2 ^ idx)) % 2)

def SignatureSpec (width numVars : Nat) (table : List Nat) (expr : Expr) : Prop :=
  ∀ assignment, assignment < 2 ^ numVars ->
    Expr.eval width (boolEnv width assignment) expr =
      BitVec.ofNat width (table.getD assignment 0)

theorem const_matches_constant_signature
    (width numVars value : Nat) (table : List Nat) :
    (∀ assignment, assignment < 2 ^ numVars -> table.getD assignment 0 = value) ->
    SignatureSpec width numVars table (Expr.const value) := by
  intro h assignment hlt
  simp [Expr.eval]
  change BitVec.ofNat width value = BitVec.ofNat width (table.getD assignment 0)
  rw [h assignment hlt]

end Cobra
