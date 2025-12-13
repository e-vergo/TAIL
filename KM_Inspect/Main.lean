/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KM_Inspect.Types
import KM_Inspect.Config
import KM_Inspect.FileUtils
import KM_Inspect.Report
import KM_Inspect.Checks.Structure
import KM_Inspect.Checks.Soundness
import KM_Inspect.Checks.ProofMinimality
import KM_Inspect.Checks.Imports
import KM_Inspect.Checks.MainTheoremPurity
import KM_Inspect.Checks.Lean4Checker

/-!
# KM_Inspect Main

CLI entry point and orchestration for Kim Morrison Standard verification.

## Usage

```bash
lake exe kmverify [directory] [--json]
```

If directory is not provided, uses current directory.
Project prefix is auto-detected from lakefile.lean.
-/

namespace KM_Inspect

open Lean Meta

/-! ## Statistics Collection -/

/-- Collect project statistics (simplified for strict Kim Morrison standard) -/
def collectStats (resolved : ResolvedConfig) : IO ProjectStats := do
  -- MainTheorem
  let mainLines ← countLines resolved.mainTheoremPath
  let mainStats : TierStats := { fileCount := 1, lineCount := mainLines }

  -- ProofOfMainTheorem
  let proofOfMainLines ← countLines resolved.proofOfMainTheoremPath
  let proofOfMainStats : TierStats := { fileCount := 1, lineCount := proofOfMainLines }

  return {
    mainTheorem := mainStats
    proofOfMainTheorem := proofOfMainStats
  }

/-! ## Check Orchestration -/

/-- Run IO-based checks (no MetaM required) -/
def runIOChecks (resolved : ResolvedConfig) : IO (List CheckResult) := do
  let lean4checker ← Checks.checkLean4Checker resolved
  return [lean4checker]

/-- Run all MetaM-based checks (environment introspection) -/
def runMetaChecks (resolved : ResolvedConfig) : MetaM (List CheckResult) := do
  let structure_ ← Checks.checkStructure resolved
  let soundness ← Checks.checkSoundness resolved
  let proofMinimality ← Checks.checkProofMinimality resolved
  let mainPurity ← Checks.checkMainTheoremPurity resolved
  let imports ← Checks.checkImports resolved  -- Now MetaM-based (re-import test)

  return [structure_, soundness, proofMinimality, mainPurity, imports]

/-- Run all checks and build report -/
def runVerification (resolved : ResolvedConfig) : MetaM VerificationReport := do
  -- Run IO checks
  let ioChecks ← runIOChecks resolved

  -- Run Meta checks (environment-based)
  let metaChecks ← runMetaChecks resolved

  -- Combine in display order
  let allChecks := metaChecks ++ ioChecks

  -- Collect stats
  let stats ← collectStats resolved

  -- Check if all passed
  let allPassed := allChecks.all (·.passed)

  return {
    projectName := resolved.projectPrefix
    checks := allChecks
    stats := stats
    allPassed := allPassed
  }

/-! ## CLI Entry Point -/

/-- Parsed CLI arguments -/
structure CLIArgs where
  projectRoot : System.FilePath := "."
  format : OutputFormat := .text
  outputPath : Option System.FilePath := none
  deriving Repr

/-- Parse command line arguments -/
def parseArgs (args : List String) : IO CLIArgs := do
  let mut result : CLIArgs := {}
  let mut i := 0
  let argsArray := args.toArray

  while i < argsArray.size do
    let arg := argsArray[i]!
    if arg == "--json" then
      result := { result with format := .json }
    else if arg == "--text" then
      result := { result with format := .text }
    else if arg == "--output" || arg == "-o" then
      i := i + 1
      if i < argsArray.size then
        result := { result with outputPath := some argsArray[i]! }
    else if arg == "--help" || arg == "-h" then
      IO.println "Usage: lake exe kmverify [directory] [--json] [--output FILE]"
      IO.println ""
      IO.println "Verify a Lean project follows the Kim Morrison Standard."
      IO.println ""
      IO.println "Arguments:"
      IO.println "  directory    Project root (default: current directory)"
      IO.println "               Project prefix is auto-detected from lakefile.lean"
      IO.println ""
      IO.println "Options:"
      IO.println "  --json       Output in JSON format"
      IO.println "  --text       Output in text format (default)"
      IO.println "  -o, --output Write output to FILE"
      IO.println "  -h, --help   Show this help"
      IO.Process.exit 0
    else if !arg.startsWith "-" then
      result := { result with projectRoot := arg }
    i := i + 1

  return result

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  let cliArgs ← parseArgs args

  -- Resolve configuration from directory (auto-detects project prefix from lakefile)
  let configResult ← resolveFromDirectory cliArgs.projectRoot

  match configResult with
  | .error e =>
    IO.eprintln s!"Error: {e}"
    return (2 : UInt32)  -- Exit code 2 for config error
  | .ok resolved =>
    -- Build the project module to get access to environment
    let proofModule := s!"{resolved.projectPrefix}.ProofOfMainTheorem"
    let imports : Array Lean.Import := #[{ module := proofModule.toName }]

    try
      -- Initialize search path from LEAN_PATH environment variable
      Lean.initSearchPath (← Lean.findSysroot)

      let env ← Lean.importModules imports {}

      let (report, _) ← Lean.Core.CoreM.toIO
        (ctx := { fileName := "KM_Inspect", fileMap := default, options := {} })
        (s := { env })
        (Lean.Meta.MetaM.run' (runVerification resolved))

      printReport report cliArgs.format cliArgs.outputPath

      return if report.allPassed then (0 : UInt32) else (1 : UInt32)
    catch e =>
      IO.eprintln s!"Error loading project: {e}"
      IO.eprintln "Make sure to run 'lake build' first."
      return (3 : UInt32)  -- Exit code 3 for build error

end KM_Inspect

/-- Entry point when run with `lean --run` -/
def main (args : List String) : IO UInt32 :=
  KM_Inspect.main args
