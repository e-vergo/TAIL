module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesRflAndTrivial
Uses rfl and trivial
-/

@[expose] public section

def StatementOfTheorem : Prop := (1 = 1) ∧ True
