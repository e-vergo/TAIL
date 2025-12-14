module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/ComplexValidProof
Substantive proof using Mathlib
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n + 0 = n ∧ 0 + n = n
