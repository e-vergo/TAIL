module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/MainTheoremPurity/OnlyDefs
MainTheorem.lean has only defs, no theorems
-/

@[expose] public section

def StatementOfTheorem : Prop := True
