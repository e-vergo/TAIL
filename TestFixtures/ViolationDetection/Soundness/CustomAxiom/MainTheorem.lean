module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/Soundness/CustomAxiom
VIOLATION: Defines and uses custom axiom
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n < n + 1
