module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: ViolationDetection/Soundness/UseNativeDecide
VIOLATION: Proof uses native_decide
-/

@[expose] public section

def StatementOfTheorem : Prop := 1 + 1 = 2
