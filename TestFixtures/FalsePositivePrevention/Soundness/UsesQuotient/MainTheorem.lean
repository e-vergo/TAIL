module

public import Mathlib.Logic.Basic

/-
Test fixture: FalsePositivePrevention/Soundness/UsesQuotient
Uses Quotient.sound - a standard axiom
-/

@[expose] public section

def mySetoid : Setoid Nat where
  r := fun a b => a % 2 = b % 2
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def StatementOfTheorem : Prop := Quotient.mk mySetoid 0 = Quotient.mk mySetoid 2
