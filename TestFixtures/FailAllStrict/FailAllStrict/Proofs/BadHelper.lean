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

axiom math_is_hard : 1 + 2 = 4

/-- VIOLATION: opaque declaration in source file -/
opaque opaqueViolation : Nat

/-- VIOLATION: @[implemented_by] attribute -/
def implFunc : Nat → Nat := fun _ => 0
@[implemented_by implFunc]
def badImplementedBy (n : Nat) : Nat := n + 1

end

end FailAllStrict
