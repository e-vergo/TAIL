/-
Proofs/BadHelper.lean - VIOLATES PROOFS PURITY:
1. Contains a structure (not allowed in Proofs/)
2. Contains a non-Prop definition (not allowed in Proofs/)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FailAllStrict

public section

/-- VIOLATION: structure not allowed in Proofs/ -/
structure BadStructure where
  value : ℕ

/-- VIOLATION: non-Prop def not allowed in Proofs/ -/
def badNonPropDef : ℕ := 100

/-- This is allowed: Prop-valued definition -/
def allowedPropDef : Prop := True

/-- This is allowed: helper lemma -/
lemma sum_cubes_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), k ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  sorry  -- For test purposes

end

end FailAllStrict
