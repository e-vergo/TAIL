module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesDecide
Uses decide tactic (kernel verified)
-/

@[expose] public section

def StatementOfTheorem : Prop := 1 + 1 = 2
