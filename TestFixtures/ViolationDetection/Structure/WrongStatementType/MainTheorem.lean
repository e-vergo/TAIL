module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/Structure/WrongStatementType
VIOLATION: StatementOfTheorem is Nat, not Prop
-/

@[expose] public section

-- Violation: StatementOfTheorem should be Prop, not Nat
def StatementOfTheorem : Nat := 42
