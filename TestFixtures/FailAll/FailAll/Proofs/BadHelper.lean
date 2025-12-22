/-
Proofs/BadHelper.lean - VIOLATES:
1. Proofs Purity: contains a structure (not allowed)
2. Proofs Purity: contains a def that doesn't return Prop
-/
import Mathlib.Tactic

namespace FailAll.Proofs

/-- VIOLATION: structures not allowed in Proofs/ -/
structure BadStructure where
  x : Nat
  y : Nat

/-- VIOLATION: def must return Prop in Proofs/ -/
def badDataDef : Nat := 42

/-- This is fine - def returning Prop -/
def goodPropDef : Prop := True

/-- This lemma is fine -/
lemma goodLemma : 1 + 1 = 2 := rfl

axiom bad : 1 + 3 = 2

end FailAll.Proofs
