module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ModuleVisibility/WrongImportType
VIOLATION: Uses public import for helper_lemmas instead of import all
-/

@[expose] public section

def StatementOfTheorem : Prop := True
