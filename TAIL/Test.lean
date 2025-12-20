/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.TestHarness

/-!
# TAIL Test Suite

Test suite for verifying TAIL checks correctly detect violations.
Run with: lake exe tailtest
-/

namespace TAIL.Test

/-- All test cases for the TAIL verification checks -/
def allTestCases : List TestCase := [
  -- ========================================
  -- VIOLATION DETECTION TESTS
  -- ========================================

  -- Structure violations
  { fixtureDir := "TestFixtures/ViolationDetection/Structure/MissingStatement"
    checkType := .structure
    expectFailure := true
    expectedMessage := "StatementOfTheorem" },
  { fixtureDir := "TestFixtures/ViolationDetection/Structure/WrongStatementType"
    checkType := .structure
    expectFailure := true
    expectedMessage := "Prop" },
  { fixtureDir := "TestFixtures/ViolationDetection/Structure/NonMathlibImport"
    checkType := .structure
    expectFailure := true
    expectedMessage := "import" },

  -- Soundness violations
  { fixtureDir := "TestFixtures/ViolationDetection/Soundness/UseSorry"
    checkType := .soundness
    expectFailure := true
    expectedMessage := "sorry" },
  { fixtureDir := "TestFixtures/ViolationDetection/Soundness/UseNativeDecide"
    checkType := .soundness
    expectFailure := true
    expectedMessage := "non-standard" },
  { fixtureDir := "TestFixtures/ViolationDetection/Soundness/CustomAxiom"
    checkType := .soundness
    expectFailure := true
    expectedMessage := "axiom" },
  { fixtureDir := "TestFixtures/ViolationDetection/Soundness/OpaqueDef"
    checkType := .soundness
    expectFailure := true
    expectedMessage := "Opaque" },

  -- ProofMinimality violations
  { fixtureDir := "TestFixtures/ViolationDetection/ProofMinimality/MultipleTheorems"
    checkType := .proofMinimality
    expectFailure := true
    expectedMessage := "invalid" },
  { fixtureDir := "TestFixtures/ViolationDetection/ProofMinimality/ExtraDefinition"
    checkType := .proofMinimality
    expectFailure := true
    expectedMessage := none },
  { fixtureDir := "TestFixtures/ViolationDetection/ProofMinimality/ZeroTheorems"
    checkType := .proofMinimality
    expectFailure := true
    expectedMessage := "invalid" },

  -- MainTheoremIsIsolated violations
  { fixtureDir := "TestFixtures/ViolationDetection/MainTheoremIsIsolated/TheoremInStatement"
    checkType := .mainTheoremIsIsolated
    expectFailure := true
    expectedMessage := "disallowed" },

  -- ModuleVisibility violations
  { fixtureDir := "TestFixtures/ViolationDetection/ModuleVisibility/LeakedHelper"
    checkType := .moduleVisibility
    expectFailure := true
    expectedMessage := "leaked" },
  { fixtureDir := "TestFixtures/ViolationDetection/ModuleVisibility/MissingModuleKeyword"
    checkType := .moduleVisibility
    expectFailure := true
    expectedMessage := "leaked" },
  { fixtureDir := "TestFixtures/ViolationDetection/ModuleVisibility/WrongImportType"
    checkType := .moduleVisibility
    expectFailure := true
    expectedMessage := "leaked" },
  { fixtureDir := "TestFixtures/ViolationDetection/ModuleVisibility/MissingExpose"
    checkType := .moduleVisibility
    expectFailure := true
    expectedMessage := "leaked" },
  { fixtureDir := "TestFixtures/ViolationDetection/ModuleVisibility/HelperNotInModule"
    checkType := .moduleVisibility
    expectFailure := true
    expectedMessage := "leaked" },

  -- ========================================
  -- FALSE POSITIVE PREVENTION TESTS
  -- ========================================

  -- Structure (valid fixtures)
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Structure/ValidBasic"
    checkType := .structure
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Structure/MultipleMathlibImports"
    checkType := .structure
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Structure/AllowedImports"
    checkType := .structure
    expectFailure := false
    expectedMessage := none },

  -- Soundness (valid fixtures)
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesStandardAxioms"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesDecide"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesClassicalLogic"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesQuotient"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/DeepDependencyChain"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesSimpWithMathlib"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/UsesRflAndTrivial"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/Soundness/ComplexValidProof"
    checkType := .soundness
    expectFailure := false
    expectedMessage := none },

  -- ProofMinimality (valid fixtures)
  { fixtureDir := "TestFixtures/FalsePositivePrevention/ProofMinimality/ExactlyOneTheorem"
    checkType := .proofMinimality
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/ProofMinimality/WithInternalAux"
    checkType := .proofMinimality
    expectFailure := false
    expectedMessage := none },

  -- MainTheoremIsIsolated (valid fixtures)
  { fixtureDir := "TestFixtures/FalsePositivePrevention/MainTheoremIsIsolated/OnlyDefs"
    checkType := .mainTheoremIsIsolated
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/MainTheoremIsIsolated/MultipleHelperDefs"
    checkType := .mainTheoremIsIsolated
    expectFailure := false
    expectedMessage := none },

  -- ModuleVisibility (valid fixtures)
  { fixtureDir := "TestFixtures/FalsePositivePrevention/ModuleVisibility/ProperModuleSystem"
    checkType := .moduleVisibility
    expectFailure := false
    expectedMessage := none },
  { fixtureDir := "TestFixtures/FalsePositivePrevention/ModuleVisibility/PublicReexports"
    checkType := .moduleVisibility
    expectFailure := false
    expectedMessage := none }
]

end TAIL.Test

/-- Entry point -/
def main (_args : List String) : IO UInt32 :=
  TAIL.Test.runAllTests TAIL.Test.allTestCases
