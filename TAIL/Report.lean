/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config

/-!
# TAIL Report Formatting

Human-readable and JSON output formatting.
-/

namespace TAIL

open Lean

/-! ## Constants -/

def tailVersion : String := "0.1"

private def lineWidth : Nat := 80
private def divider : String := String.ofList (List.replicate lineWidth '=')
private def thinDivider : String := String.ofList (List.replicate lineWidth '-')

/-! ## Output Format -/

/-- Output format options -/
inductive OutputFormat where
  | text
  | json
  deriving DecidableEq, Repr

/-! ## Formatting Helpers -/

/-- Pad a string to a given width -/
private def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - min s.length width) ' ')

/-- Format a number with thousands separator (simple version) -/
private def formatNumber (n : Nat) : String :=
  toString n

/-! ## Human-Readable Output -/

/-- Get current timestamp -/
private def getTimestamp : IO String := do
  let output ← IO.Process.output { cmd := "date", args := #["+%Y-%m-%d %H:%M:%S"] }
  return output.stdout.trimAscii.toString

/-- Format the header -/
def formatHeader (projectName : String) : String :=
  s!"{divider}\n" ++
  s!"KIM MORRISON STANDARD COMPLIANCE REPORT\n" ++
  s!"Project: {projectName}\n" ++
  s!"Tool: TAIL v{tailVersion}\n" ++
  s!"{divider}\n"

/-- Format trust tier summary -/
def formatTierSummary (stats : ProjectStats) : String :=
  let hasDefinitions := stats.definitions.lineCount > 0
  let hasProofs := stats.proofs.lineCount > 0

  let modeLabel := if hasDefinitions then "EXTENDED KIM MORRISON STANDARD" else "STRICT KIM MORRISON STANDARD"
  let header := s!"\nTRUST TIER SUMMARY ({modeLabel})\n" ++ thinDivider ++ "\n"

  -- Human Review Tier
  let humanReviewHeader := "  [HUMAN REVIEW]\n"
  let mainThmLine := s!"    MainTheorem.lean                            {formatNumber stats.mainTheorem.lineCount} lines\n"
  let defsLine := if hasDefinitions then
    s!"    Definitions/ ({stats.definitions.fileCount} files)                     {formatNumber stats.definitions.lineCount} lines\n"
  else ""

  -- Machine Verified Tier
  let machineHeader := "  [MACHINE VERIFIED]\n"
  let proofLine := s!"    ProofOfMainTheorem.lean                     {formatNumber stats.proofOfMainTheorem.lineCount} lines\n"
  let proofsLine := if hasProofs then
    s!"    Proofs/ ({stats.proofs.fileCount} files)                         {formatNumber stats.proofs.lineCount} lines\n"
  else ""

  let separator := thinDivider ++ "\n"

  -- Review burden
  let total := stats.totalLines
  let review := stats.reviewBurden
  let pct := if total > 0 then (review * 100) / total else 0

  let reviewDesc := if hasDefinitions then
    s!"  REVIEW BURDEN: {formatNumber review} lines (MainTheorem.lean + Definitions/)\n"
  else
    s!"  REVIEW BURDEN: {formatNumber review} lines (MainTheorem.lean only)\n"

  let totalLine := s!"  TOTAL: {formatNumber total} lines ({pct}% requires review)\n"

  header ++
  humanReviewHeader ++ mainThmLine ++ defsLine ++
  machineHeader ++ proofLine ++ proofsLine ++
  separator ++ reviewDesc ++ totalLine

/-- Format a single check result -/
def formatCheck (result : CheckResult) : String :=
  let status := if result.passed then "[PASS]" else "[FAIL]"
  let line := s!"  {status} {result.name}"

  if result.passed then
    line ++ "\n"
  else
    let detailLines := result.details.map (s!"         " ++ ·)
    line ++ "\n" ++ String.intercalate "\n" detailLines ++
    (if detailLines.isEmpty then "" else "\n")

/-- Format all check results -/
def formatChecks (checks : List CheckResult) : String :=
  let header := "\nCHECKS\n" ++ thinDivider ++ "\n"
  let body := String.intercalate "" (checks.map formatCheck)
  header ++ body

/-- Format the final result -/
def formatResult (allPassed : Bool) : String :=
  let result := if allPassed then
    "\n" ++ divider ++ "\n" ++
    "RESULT: PROJECT MEETS TEMPLATE EXPECTATIONS\n" ++
    "\nThis project meets the Kim Morrison Standard for AI-assisted formal proofs.\n" ++
    "A human reviewer only needs to verify MainTheorem.lean to trust the result.\n" ++
    divider ++ "\n"
  else
    "\n" ++ divider ++ "\n" ++
    "RESULT: PROJECT FAILS TO MEET TEMPLATE EXPECTATIONS\n" ++
    "\nPlease fix the issues above before requesting review.\n" ++
    divider ++ "\n"
  result

/-- Format a complete verification report -/
def formatReport (report : VerificationReport) : String :=
  formatHeader report.projectName ++
  formatTierSummary report.stats ++
  formatChecks report.checks ++
  formatResult report.allPassed

/-! ## JSON Output -/

/-- Calculate review percentage -/
private def reviewPercentage (stats : ProjectStats) : Float :=
  let total := stats.totalLines
  let review := stats.reviewBurden
  if total > 0 then
    (review.toFloat / total.toFloat) * 100.0
  else 0.0

/-- Format report as pretty-printed JSON with enhanced structure -/
def formatReportJson (report : VerificationReport) : String :=
  let result := if report.allPassed then "VERIFIED" else "FAILED"
  let pct := reviewPercentage report.stats
  let hasDefinitions := report.stats.definitions.lineCount > 0
  let standardName := if hasDefinitions then "Kim Morrison Extended" else "Kim Morrison Strict"

  -- Build enhanced JSON structure
  let json := Json.mkObj [
    ("version", toJson tailVersion),
    ("standard", toJson standardName),
    ("project", toJson report.projectName),
    ("result", toJson result),
    ("stats", Json.mkObj [
      ("main_theorem", toJson report.stats.mainTheorem),
      ("definitions", toJson report.stats.definitions),
      ("proof_of_main_theorem", toJson report.stats.proofOfMainTheorem),
      ("proofs", toJson report.stats.proofs),
      ("total_lines", toJson report.stats.totalLines),
      ("review_burden", toJson report.stats.reviewBurden),
      ("review_percentage", toJson pct)
    ]),
    ("checks", toJson report.checks),
    ("all_passed", toJson report.allPassed)
  ]

  json.pretty

/-! ## Console Output -/

/-- Print the report to stdout or file -/
def printReport (report : VerificationReport) (format : OutputFormat := .text)
    (outputPath : Option System.FilePath := none) : IO Unit := do
  let content := match format with
    | .text => formatReport report
    | .json => formatReportJson report

  match outputPath with
  | some path => IO.FS.writeFile path content
  | none => IO.println content

end TAIL
