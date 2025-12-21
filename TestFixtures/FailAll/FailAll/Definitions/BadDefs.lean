/-
Definitions/BadDefs.lean - VIOLATES:
1. Definitions Purity: contains a theorem (not allowed)
2. Definitions Purity: contains sorry
-/
import Mathlib.Tactic

namespace FailAll.Definitions

/-- This def is fine -/
def goodDef : Nat := 42

/-- VIOLATION: theorems not allowed in Definitions/ -/
theorem badTheoremInDefs : 1 = 1 := rfl

/-- VIOLATION: sorry not allowed in Definitions/ -/
def badDefWithSorry : Nat := by
  sorry

end FailAll.Definitions
