/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Checks.Structure
import TAIL.Checks.Soundness
import TAIL.Checks.ProofMinimality
import TAIL.Checks.MainTheoremPurity
import TAIL.Checks.Imports

/-!
# TAIL Test Harness

Test infrastructure for verifying that TAIL checks correctly detect violations.
-/

namespace TAIL.Test

open Lean Meta

/-- Check if a string contains a substring -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Repeat a string n times -/
def repeatStr (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)

/-- Which check to run on a fixture -/
inductive CheckType where
  | structure
  | soundness
  | proofMinimality
  | mainTheoremPurity
  | moduleVisibility
  deriving DecidableEq, Repr

instance : ToString CheckType where
  toString
    | .structure => "Structure"
    | .soundness => "Soundness"
    | .proofMinimality => "ProofMinimality"
    | .mainTheoremPurity => "MainTheoremPurity"
    | .moduleVisibility => "ModuleVisibility"

/-- A test case definition -/
structure TestCase where
  /-- Directory path relative to project root, e.g., "TestFixtures/Structure/MissingStatement" -/
  fixtureDir : String
  /-- Which check this tests -/
  checkType : CheckType
  /-- Expected to fail (true) or pass (false) -/
  expectFailure : Bool
  /-- Optional substring expected in error message -/
  expectedMessage : Option String := none
  deriving Repr

/-- Result of running a single test -/
structure TestResult where
  testCase : TestCase
  passed : Bool
  message : String
  deriving Repr

/-- Create ResolvedConfig for a test fixture.
    Handles nested directory paths like "TestFixtures/Structure/MissingStatement" -/
def makeFixtureConfig (fixtureDir : String) (mode : VerificationMode := .default) : IO ResolvedConfig := do
  let root ← IO.currentDir
  let fixturePath := root / fixtureDir
  -- Convert path separators to dots for module name
  let modulePrefix := fixtureDir.replace "/" "."
  -- Check for optional folders
  let definitionsPath := fixturePath / definitionsFolder
  let definitionsExists ← definitionsPath.pathExists
  let proofsPath := fixturePath / proofsFolder
  let proofsExists ← proofsPath.pathExists
  return {
    mode := mode
    projectPrefix := modulePrefix
    projectRoot := root
    sourcePath := fixturePath
    mainTheoremPath := fixturePath / "MainTheorem.lean"
    proofOfMainTheoremPath := fixturePath / "ProofOfMainTheorem.lean"
    definitionsPath := if definitionsExists then some definitionsPath else none
    proofsPath := if proofsExists then some proofsPath else none
  }

/-- Run the appropriate check for the given CheckType -/
def runCheck (checkType : CheckType) (resolved : ResolvedConfig) : MetaM CheckResult := do
  match checkType with
  | .structure => Checks.checkStructure resolved
  | .soundness => Checks.checkSoundness resolved
  | .proofMinimality => Checks.checkProofMinimality resolved
  | .mainTheoremPurity => Checks.checkMainTheoremPurity resolved
  | .moduleVisibility => Checks.checkImports resolved

/-- Run a single test case and return result -/
def runTestCase (tc : TestCase) : IO TestResult := do
  let resolved ← makeFixtureConfig tc.fixtureDir

  -- Load the environment for this fixture
  let proofModule := s!"{resolved.projectPrefix}.ProofOfMainTheorem"
  let imports : Array Lean.Import := #[{ module := proofModule.toName }]

  try
    Lean.initSearchPath (← Lean.findSysroot)
    let env ← Lean.importModules imports {}

    let (checkResult, _) ← Lean.Core.CoreM.toIO
      (ctx := { fileName := "TAIL.Test", fileMap := default, options := {} })
      (s := { env })
      (Lean.Meta.MetaM.run' (runCheck tc.checkType resolved))

    -- Evaluate test result
    let checkFailed := !checkResult.passed

    if tc.expectFailure then
      -- We expected the check to fail
      if checkFailed then
        -- Check passed - the check correctly detected the violation
        match tc.expectedMessage with
        | some expected =>
          if containsSubstr checkResult.message expected then
            return { testCase := tc, passed := true, message := "Check correctly failed with expected message" }
          else
            return { testCase := tc, passed := false,
                     message := s!"Check failed but message didn't contain '{expected}'. Got: {checkResult.message}" }
        | none =>
          return { testCase := tc, passed := true, message := "Check correctly detected violation" }
      else
        -- Test failed - the check didn't catch the violation (false negative!)
        return { testCase := tc, passed := false,
                 message := s!"FALSE NEGATIVE: Check passed but should have failed. Message: {checkResult.message}" }
    else
      -- We expected the check to pass
      if checkFailed then
        return { testCase := tc, passed := false,
                 message := s!"Check failed but should have passed: {checkResult.message}" }
      else
        return { testCase := tc, passed := true, message := "Check correctly passed" }

  catch e =>
    return { testCase := tc, passed := false, message := s!"Error loading fixture: {e}" }

/-- Run all test cases and report results -/
def runAllTests (testCases : List TestCase) : IO UInt32 := do
  let separator := repeatStr "=" 70
  let sectionHeader := repeatStr "─" 70

  -- Partition tests by category
  let violationTests := testCases.filter (·.expectFailure)
  let validTests := testCases.filter (!·.expectFailure)

  -- Collect output lines for both console and file
  let mut outputLines : List String := []
  outputLines := outputLines ++ [separator, "TAIL TEST HARNESS", separator]

  -- Counters
  let mut violationsPassed := 0
  let mut violationsFailed := 0
  let mut validPassed := 0
  let mut validFailed := 0

  -- Process violation detection tests
  outputLines := outputLines ++ ["", s!"── VIOLATION DETECTION TESTS {sectionHeader.drop 29}"]
  outputLines := outputLines ++ ["These fixtures contain intentional violations that TAIL should detect.", ""]

  for tc in violationTests do
    let result ← runTestCase tc
    let (icon, status) := if result.passed
      then ("✓", "VIOLATION detected (expected)")
      else ("✗", "NO VIOLATION detected (expected VIOLATION)")
    outputLines := outputLines ++ [s!"{icon} {status} - {tc.fixtureDir} ({tc.checkType})"]
    if !result.passed then
      outputLines := outputLines ++ [s!"    {result.message}"]
    if result.passed then violationsPassed := violationsPassed + 1
    else violationsFailed := violationsFailed + 1

  -- Process false positive prevention tests
  outputLines := outputLines ++ ["", s!"── FALSE POSITIVE PREVENTION TESTS {sectionHeader.drop 35}"]
  outputLines := outputLines ++ ["These fixtures are valid and should pass all checks.", ""]

  for tc in validTests do
    let result ← runTestCase tc
    let (icon, status) := if result.passed
      then ("✓", "COMPLIANT (expected)")
      else ("✗", "VIOLATION detected (expected COMPLIANT)")
    outputLines := outputLines ++ [s!"{icon} {status} - {tc.fixtureDir} ({tc.checkType})"]
    if !result.passed then
      outputLines := outputLines ++ [s!"    {result.message}"]
    if result.passed then validPassed := validPassed + 1
    else validFailed := validFailed + 1

  -- Summary
  let totalPassed := violationsPassed + validPassed
  let totalTests := testCases.length
  let dash := repeatStr "-" 70
  outputLines := outputLines ++ [
    "", dash,
    s!"Violation Detection: {violationsPassed}/{violationTests.length} violations correctly detected",
    s!"False Positive Prevention: {validPassed}/{validTests.length} valid fixtures correctly passed",
    s!"Total: {totalPassed}/{totalTests} tests passed",
    separator
  ]

  -- Print to console
  for line in outputLines do
    IO.println line

  -- Write report to file
  let reportPath := "tail_test_report.txt"
  let reportContent := String.intercalate "\n" outputLines
  IO.FS.writeFile reportPath reportContent
  IO.println ""
  IO.println s!"Report written to: {reportPath}"

  return if totalPassed == totalTests then 0 else 1

end TAIL.Test
