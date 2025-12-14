module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesSimpWithMathlib
Uses simp with Mathlib lemmas
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n + 0 = n
