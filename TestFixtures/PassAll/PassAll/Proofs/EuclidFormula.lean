module

public import Mathlib.Tactic

namespace PassAll

public section

/-- The core algebraic identity for Euclid's formula:
    (m² - n²)² + (2mn)² = (m² + n²)²

This works in any commutative ring, but we state it for ℤ to handle
the subtraction properly before transferring to ℕ.
-/
lemma euclid_identity_int (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  ring

/-- Euclid's formula produces a valid Pythagorean equation for natural numbers.
    Given m > n > 0, we have (m² - n²)² + (2mn)² = (m² + n²)²
-/
lemma euclid_identity_nat {m n : ℕ} (h : n < m) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  -- Lift to integers where subtraction is well-behaved
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt h) 2
  zify [hle]
  ring

/-! ## False-Negative Tests

These tests verify that keywords in comments, strings, and names don't trigger
false positives from the source-based checks.
-/

/-- This helper doesn't use any axiom or sorry - just pure math.
    The word "axiom" in this comment should be ignored.
    Similarly, "sorry" and "opaque" and "unsafe" are just words here. -/
def axiom_mention_helper : Prop := True

-- Comment: axiom bad : 1 = 2
-- Comment: sorry
-- Comment: opaque sneaky : Nat
-- Comment: unsafe def evil : Nat := 42

/-- A string containing keywords should not trigger detection -/
def string_with_keywords : String := "axiom sorry opaque unsafe native_decide implemented_by"

end

end PassAll
