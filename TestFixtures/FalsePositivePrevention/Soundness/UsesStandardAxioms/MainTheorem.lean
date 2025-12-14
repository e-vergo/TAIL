module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesStandardAxioms
Uses propext (standard axiom)
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ p q : Prop, (p ↔ q) → p = q
