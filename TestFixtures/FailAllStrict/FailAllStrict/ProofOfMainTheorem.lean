/-
ProofOfMainTheorem.lean - VIOLATES CHECKS:
1. Soundness: uses sorry
2. Proof Minimality: has multiple public theorems
-/
import FailAllStrict.MainTheorem

namespace FailAllStrict

/-- The main theorem -/
theorem mainTheorem : StatementOfTheorem := by
  sorry  -- VIOLATION: uses sorry (Soundness)

/-- VIOLATION: extra public theorem (Proof Minimality) -/
theorem extraTheorem : True := trivial

/-- VIOLATION: another extra theorem -/
theorem anotherExtraTheorem : 2 + 2 = 4 := rfl

end FailAllStrict
