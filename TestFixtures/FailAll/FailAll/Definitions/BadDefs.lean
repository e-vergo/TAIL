/-
Definitions/BadDefs.lean - VIOLATES:
1. Soundness: contains sorry (caught by global Soundness check)
2. Unsafe Attributes: contains @[implemented_by]
3. Semantic Warnings: contains notation (triggers review warning)
4. Semantic Warnings: contains macro (triggers review warning)

Note: Theorems ARE allowed in Definitions/ (needed for dependent definitions)
-/
import Mathlib.Tactic

namespace FailAll.Definitions

/-- This def is fine -/
def goodDef : Nat := 42

/-- This theorem is fine - theorems allowed in Definitions/ -/
theorem allowedTheoremInDefs : 1 = 1 := rfl

/-- VIOLATION: sorry not allowed in Definitions/ -/
def badDefWithSorry : Nat := by
  sorry

/-- Implementation function for implemented_by -/
def implFunc : Nat := 100

/-- VIOLATION: implemented_by bypasses kernel verification -/
@[implemented_by implFunc]
def badImplementedBy : Nat := 42

/-- WARNING: notation can mislead readers of MainTheorem.lean -/
notation "misleading_syntax" => True

/-- WARNING: macro can affect how MainTheorem.lean is interpreted -/
macro "badMacro" : term => `(42)

end FailAll.Definitions
