module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/MainTheoremPurity/TheoremInStatement
VIOLATION: MainTheorem.lean contains a theorem
-/

@[expose] public section

def StatementOfTheorem : Prop := True

-- VIOLATION: theorem in MainTheorem.lean
theorem disallowedTheorem : True := trivial
