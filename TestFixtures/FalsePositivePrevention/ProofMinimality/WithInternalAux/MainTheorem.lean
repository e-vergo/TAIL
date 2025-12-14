module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/ProofMinimality/WithInternalAux
Uses match which creates internal aux declarations
-/

@[expose] public section

def StatementOfTheorem : Prop := ∀ n : Nat, n = n
