module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/Soundness/UseSorry
VIOLATION: Proof uses sorry
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n = n
