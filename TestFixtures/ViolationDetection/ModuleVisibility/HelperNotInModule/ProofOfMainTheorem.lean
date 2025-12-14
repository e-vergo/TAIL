/-
Test fixture: ViolationDetection/ModuleVisibility/HelperNotInModule
VIOLATION: helper_lemmas.lean doesn't use module keyword
-/
-- Can't be a module since we import a non-module helper_lemmas
import Mathlib.Logic.Basic
import TestFixtures.ViolationDetection.ModuleVisibility.HelperNotInModule.MainTheorem
import TestFixtures.ViolationDetection.ModuleVisibility.HelperNotInModule.Proofs.helper_lemmas

theorem mainTheorem : StatementOfTheorem := trivial
