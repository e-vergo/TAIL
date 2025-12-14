module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ModuleVisibility/MissingModuleKeyword
VIOLATION: ProofOfMainTheorem missing module keyword
-/

@[expose] public section

def StatementOfTheorem : Prop := True
