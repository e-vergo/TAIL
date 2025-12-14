module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/ModuleVisibility/ProperModuleSystem
Uses module system correctly
-/

@[expose] public section

def StatementOfTheorem : Prop := True
