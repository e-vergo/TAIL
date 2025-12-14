module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ModuleVisibility/MissingExpose
VIOLATION: mainTheorem not in @[expose] public section
-/

@[expose] public section

def StatementOfTheorem : Prop := True
