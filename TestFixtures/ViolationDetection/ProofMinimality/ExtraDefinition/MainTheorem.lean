module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/ProofMinimality/ExtraDefinition
VIOLATION: ProofOfMainTheorem contains extra definition
-/

@[expose] public section

def StatementOfTheorem : Prop := True
