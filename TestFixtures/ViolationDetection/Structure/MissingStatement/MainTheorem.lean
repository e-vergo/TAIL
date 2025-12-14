module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/Structure/MissingStatement
VIOLATION: No StatementOfTheorem defined
-/

@[expose] public section

-- Violation: StatementOfTheorem is NOT defined
def SomethingElse : Prop := True
