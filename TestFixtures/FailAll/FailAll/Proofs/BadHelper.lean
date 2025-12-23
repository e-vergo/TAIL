/-
Proofs/BadHelper.lean - VIOLATES:
1. Proofs Purity: contains a structure (not allowed)
2. Proofs Purity: contains a def that doesn't return Prop
3. Soundness: contains a partial def (non-termination risk)
4. Soundness: contains an unsafe def (bypasses type checker)
5. Axioms in Source: contains an axiom declaration
6. Proofs Purity: multi-arg def not returning Prop
-/
import Mathlib.Tactic

namespace FailAll.Proofs

/-- VIOLATION: structures not allowed in Proofs/ -/
structure BadStructure where
  x : Nat
  y : Nat

/-- VIOLATION: def must return Prop in Proofs/ -/
def badDataDef : Nat := 42

/-- VIOLATION: multi-arg def not returning Prop -/
def badMultiArgDef (a : Nat) (b : Nat) : Nat := a + b

/-- This is fine - multi-arg def returning Prop -/
def goodMultiArgProp (a : Nat) (b : Nat) : Prop := a = b

/-- This is fine - def returning Prop -/
def goodPropDef : Prop := True

/-- This lemma is fine -/
lemma goodLemma : 1 + 1 = 2 := rfl

/-- VIOLATION: partial def (non-termination risk) -/
partial def badPartialDef (n : Nat) : Nat := badPartialDef n

/-- VIOLATION: unsafe def (bypasses type checker) -/
unsafe def badUnsafeDef : Nat := 42

/-- VIOLATION: axiom declaration in source file -/
axiom bad : 1 + 3 = 2

/-- VIOLATION: opaque declaration in source file -/
opaque opaqueViolation : Nat

end FailAll.Proofs
