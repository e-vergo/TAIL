module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/DeepDependencyChain
Deep proof using Mathlib lemmas
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n + 0 = n ∧ 0 + n = n
