/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KM_Inspect.Types
import KM_Inspect.Config

/-!
# KM_Inspect Report Formatting

Human-readable and JSON output formatting.
-/

namespace KM_Inspect

open Lean

/-! ## Constants -/

def kmVerifyVersion : String := "1.0.0"

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

/-- Format the header -/
def formatHeader (projectName : String) : String :=
  s!"{divider}\n" ++
  s!"KIM MORRISON STANDARD VERIFICATION\n" ++
  s!"Project: {projectName}\n" ++
  s!"{divider}\n"

/-- Format trust tier summary (strict Kim Morrison standard - only 2 tiers) -/
def formatTierSummary (stats : ProjectStats) : String :=
  let header := "\nTRUST TIER SUMMARY (STRICT KIM MORRISON STANDARD)\n" ++ thinDivider ++ "\n"

  -- MainTheorem (requires human review)
  let mainThmLine := s!"  {padRight "MainTheorem.lean" 40}{formatNumber stats.mainTheorem.lineCount} lines  [HUMAN REVIEW]\n"

  -- ProofOfMainTheorem (machine verified)
  let proofLine := s!"  {padRight "ProofOfMainTheorem.lean" 40}{formatNumber stats.proofOfMainTheorem.lineCount} lines  [MACHINE VERIFIED]\n"

  let separator := thinDivider ++ "\n"

  -- Review burden
  let total := stats.totalLines
  let review := stats.reviewBurden
  let pct := if total > 0 then (review * 100) / total else 0

  let reviewLine := s!"  REVIEW BURDEN: {formatNumber review} lines"
  let reviewDesc := " (MainTheorem.lean only)\n"
  let totalLine := s!"  TOTAL: {formatNumber total} lines ({pct}% requires review)\n"

  header ++ mainThmLine ++ proofLine ++ separator ++ reviewLine ++ reviewDesc ++ totalLine

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
    "RESULT: PROJECT VERIFIED\n" ++
    divider ++ "\n"
  else
    "\n" ++ divider ++ "\n" ++
    "RESULT: VERIFICATION FAILED\n" ++
    "Please fix the issues above before requesting review.\n" ++
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

  -- Build enhanced JSON structure (strict Kim Morrison standard - 2 tiers)
  let json := Json.mkObj [
    ("version", toJson kmVerifyVersion),
    ("standard", toJson "Kim Morrison Strict"),
    ("project", toJson report.projectName),
    ("result", toJson result),
    ("stats", Json.mkObj [
      ("main_theorem", toJson report.stats.mainTheorem),
      ("proof_of_main_theorem", toJson report.stats.proofOfMainTheorem),
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

end KM_Inspect
