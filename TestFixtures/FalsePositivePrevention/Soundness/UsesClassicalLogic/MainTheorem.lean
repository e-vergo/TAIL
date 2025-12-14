module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesClassicalLogic
Uses Classical.em (excluded middle)
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ p : Prop, p ∨ ¬p
