/-
Test fixture: ViolationDetection/ModuleVisibility/MissingModuleKeyword
VIOLATION: Missing module keyword - declarations will be visible
-/
-- VIOLATION: No module keyword
import Mathlib.Logic.Basic
import TestFixtures.ViolationDetection.ModuleVisibility.MissingModuleKeyword.MainTheorem
import TestFixtures.ViolationDetection.ModuleVisibility.MissingModuleKeyword.Proofs.helper_lemmas

-- Without module keyword, this def is visible externally
def internalHelper : Nat := 42

theorem mainTheorem : StatementOfTheorem := trivial
