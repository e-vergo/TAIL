module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Basic

/-
Test fixture: FalsePositivePrevention/MainTheoremPurity/MultipleHelperDefs
Multiple helper defs alongside StatementOfTheorem
-/

@[expose] public section

def helperDef1 : Nat := 42
def helperDef2 : Nat := 43
def StatementOfTheorem : Prop := helperDef1 < helperDef2
