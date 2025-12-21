/-
MainTheorem.lean - VIOLATES STRICT MODE CHECKS:
1. Structure: imports from Proofs/ (not allowed)
2. MainTheorem Purity: has extra def (ERROR in strict, warning in default)
3. MainTheorem Purity: has theorem (not allowed)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FailAllStrict.Proofs.BadHelper  -- VIOLATION: imports from Proofs/

namespace FailAllStrict

@[expose] public section

/-- The main theorem statement -/
def StatementOfTheorem : Prop :=
  ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), k ^ 3) = (∑ k ∈ Finset.range (n + 1), k) ^ 2

/-- VIOLATION (Strict): extra definition not allowed in strict mode -/
def ExtraDefinition : ℕ := 42

/-- VIOLATION: theorems not allowed in MainTheorem.lean -/
theorem badTheorem : True := trivial

end

end FailAllStrict
