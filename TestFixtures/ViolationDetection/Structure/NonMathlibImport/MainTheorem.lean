module

public import Mathlib.Logic.Basic

/-
Test fixture: ViolationDetection/Structure/NonMathlibImport
VIOLATION: Imports from project (not just Mathlib)
-/

-- VIOLATION: Importing from test fixtures (project code) instead of just Mathlib
-- This demonstrates importing project code which shouldn't be allowed in MainTheorem.lean
import all TestFixtures.FalsePositivePrevention.Structure.ValidBasic.Proofs.helper_lemmas

@[expose] public section

def StatementOfTheorem : Prop := True
