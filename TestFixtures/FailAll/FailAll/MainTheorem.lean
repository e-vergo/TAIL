/-
MainTheorem.lean - VIOLATES MULTIPLE CHECKS:
1. Import Discipline: imports from Proofs/ (not allowed)
2. MainTheorem Isolation: contains a theorem (not allowed)
-/
import Mathlib.Tactic
import FailAll.Proofs.BadHelper  -- VIOLATION: importing from Proofs/

namespace FailAll

/-- The statement we want to prove -/
def StatementOfTheorem : Prop := 1 + 1 = 2

/-- VIOLATION: theorems not allowed in MainTheorem.lean -/
theorem badTheorem : True := trivial

end FailAll
