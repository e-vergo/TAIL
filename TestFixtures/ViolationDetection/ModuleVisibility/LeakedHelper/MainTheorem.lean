module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ModuleVisibility/LeakedHelper
VIOLATION: Helper def leaked in public section
-/

@[expose] public section

def StatementOfTheorem : Prop := True
