module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ModuleVisibility/HelperNotInModule
VIOLATION: helper_lemmas.lean not using module keyword
-/

@[expose] public section

def StatementOfTheorem : Prop := True
