/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.FileUtils
import TAIL.Report
import TAIL.FastChecks

/-!
# TAIL Main

CLI entry point and orchestration for TAIL Standard verification.

## Usage

```bash
lake exe tailverify [directory] [--json]
```

If directory is not provided, uses current directory.
Project prefix is auto-detected from lakefile.lean.
-/

namespace TAIL

/-! ## Statistics Collection -/

/-- Count lines in all .lean files in a directory -/
def countDirLines (dir : System.FilePath) : IO TierStats := do
  let mut fileCount := 0
  let mut lineCount := 0
  let entries ← dir.readDir
  for entry in entries do
    if entry.fileName.endsWith ".lean" then
      let lines ← countLines entry.path
      fileCount := fileCount + 1
      lineCount := lineCount + lines
  return { fileCount, lineCount }

/-- Collect project statistics -/
def collectStats (resolved : ResolvedConfig) : IO ProjectStats := do
  -- MainTheorem
  let mainLines ← countLines resolved.mainTheoremPath
  let mainStats : TierStats := { fileCount := 1, lineCount := mainLines }

  -- Definitions/ (if present)
  let definitionsStats ← match resolved.definitionsPath with
    | some path => countDirLines path
    | none => pure { fileCount := 0, lineCount := 0 }

  -- ProofOfMainTheorem
  let proofOfMainLines ← countLines resolved.proofOfMainTheoremPath
  let proofOfMainStats : TierStats := { fileCount := 1, lineCount := proofOfMainLines }

  -- Proofs/ (if present)
  let proofsStats ← match resolved.proofsPath with
    | some path => countDirLines path
    | none => pure { fileCount := 0, lineCount := 0 }

  return {
    mainTheorem := mainStats
    definitions := definitionsStats
    proofOfMainTheorem := proofOfMainStats
    proofs := proofsStats
  }

/-! ## Check Orchestration -/

/-- Run all checks and build report using the fast olean-based reader -/
def runVerification (resolved : ResolvedConfig) : IO VerificationReport := do
  let checks ← FastChecks.runFastChecks resolved
  let stats ← collectStats resolved
  let allPassed := checks.all (·.passed)

  return {
    projectName := resolved.projectPrefix
    checks := checks
    stats := stats
    allPassed := allPassed
  }

/-! ## CLI Entry Point -/

/-- Parsed CLI arguments -/
structure CLIArgs where
  projectRoot : System.FilePath := "."
  format : OutputFormat := .text
  outputPath : Option System.FilePath := none
  generateReport : Bool := false  -- Auto-generate compliance report file
  projectPrefix : Option String := none  -- Override auto-detected prefix
  mode : VerificationMode := .default  -- Verification mode
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
    else if arg == "--strict" then
      result := { result with mode := .strict }
    else if arg == "--report" || arg == "-r" then
      result := { result with generateReport := true }
    else if arg == "--output" || arg == "-o" then
      i := i + 1
      if i < argsArray.size then
        result := { result with outputPath := some argsArray[i]! }
    else if arg == "--prefix" || arg == "-p" then
      i := i + 1
      if i < argsArray.size then
        result := { result with projectPrefix := some argsArray[i]! }
    else if arg == "--help" || arg == "-h" then
      IO.println "Usage: lake exe tailverify [directory] [--strict] [--prefix NAME] [--report] [--output FILE]"
      IO.println ""
      IO.println "Verify a Lean project follows the TAIL Standard."
      IO.println ""
      IO.println "Arguments:"
      IO.println "  directory    Project root (default: current directory)"
      IO.println ""
      IO.println "Options:"
      IO.println "  --strict     Strict mode: original TAIL Standard (no Definitions/ folder)"
      IO.println "  -p, --prefix Override project prefix (default: auto-detect from lakefile)"
      IO.println "  --json       Output in JSON format"
      IO.println "  --text       Output in text format (default)"
      IO.println "  -r, --report Generate tail_compliance_report.txt in project root"
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

  -- Resolve configuration (use explicit prefix if provided, otherwise auto-detect)
  let configResult ← match cliArgs.projectPrefix with
    | some pfx => resolveWithPrefix cliArgs.projectRoot pfx cliArgs.mode
    | none => resolveFromDirectory cliArgs.projectRoot cliArgs.mode

  match configResult with
  | .error e =>
    IO.eprintln s!"Error: {e}"
    return (2 : UInt32)  -- Exit code 2 for config error
  | .ok resolved =>
    try
      -- Run verification using fast olean-based checks (no environment loading needed)
      let report ← runVerification resolved

      -- Print to console
      printReport report cliArgs.format cliArgs.outputPath

      -- Generate compliance report file if requested
      if cliArgs.generateReport then
        let reportPath := cliArgs.projectRoot / "tail_compliance_report.txt"
        printReport report .text (some reportPath)
        IO.println s!"Compliance report written to: {reportPath}"

      return if report.allPassed then (0 : UInt32) else (1 : UInt32)
    catch e =>
      IO.eprintln s!"Error during verification: {e}"
      IO.eprintln "Make sure to run 'lake build' first."
      return (3 : UInt32)  -- Exit code 3 for verification error

end TAIL

/-- Entry point when run with `lean --run` -/
def main (args : List String) : IO UInt32 :=
  TAIL.main args
