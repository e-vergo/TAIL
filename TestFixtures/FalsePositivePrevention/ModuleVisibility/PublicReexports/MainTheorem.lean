module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: FalsePositivePrevention/ModuleVisibility/PublicReexports
Re-exports Mathlib publicly - allowed
-/

@[expose] public section

def StatementOfTheorem : Prop := True
