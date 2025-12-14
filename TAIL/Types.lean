/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean

/-!
# TAIL Types

Core types for Kim Morrison Standard verification.
-/

namespace TAIL

open Lean

/-! ## Trust Levels -/

/-- Trust tiers for the Kim Morrison Standard.
The strict standard has only two tiers: statement and proof. -/
inductive TrustLevel where
  /-- Statement file: Mathlib-only imports, contains only StatementOfTheorem def -/
  | MainTheorem
  /-- Proof file: uses module system, exactly one public theorem -/
  | ProofOfMainTheorem
  deriving DecidableEq, Repr, Inhabited

instance : ToString TrustLevel where
  toString
    | .MainTheorem => "MainTheorem"
    | .ProofOfMainTheorem => "ProofOfMainTheorem"

/-! ## Check Results -/

/-- Result of a single verification check -/
structure CheckResult where
  /-- Name of the check -/
  name : String
  /-- Whether the check passed -/
  passed : Bool
  /-- Human-readable message -/
  message : String
  /-- Additional details (e.g., list of violations) -/
  details : List String := []
  deriving Inhabited, Repr

instance : ToJson CheckResult where
  toJson r := Json.mkObj [
    ("name", toJson r.name),
    ("passed", toJson r.passed),
    ("message", toJson r.message),
    ("details", toJson r.details)
  ]

/-- Create a passing check result -/
def CheckResult.pass (name : String) (message : String) : CheckResult :=
  { name, passed := true, message, details := [] }

/-- Create a failing check result -/
def CheckResult.fail (name : String) (message : String) (details : List String := []) : CheckResult :=
  { name, passed := false, message, details }

/-! ## Line Count Statistics -/

/-- Line counts for a trust tier -/
structure TierStats where
  /-- Number of files in this tier -/
  fileCount : Nat
  /-- Total lines of code -/
  lineCount : Nat
  deriving Inhabited, Repr

instance : ToJson TierStats where
  toJson s := Json.mkObj [
    ("file_count", toJson s.fileCount),
    ("line_count", toJson s.lineCount)
  ]

/-- Aggregated statistics for the two trust tiers -/
structure ProjectStats where
  mainTheorem : TierStats
  proofOfMainTheorem : TierStats
  deriving Inhabited, Repr

/-- Calculate total lines in the project -/
def ProjectStats.totalLines (s : ProjectStats) : Nat :=
  s.mainTheorem.lineCount +
  s.proofOfMainTheorem.lineCount

/-- Calculate review burden (lines requiring human review).
Per Kim Morrison standard, only MainTheorem.lean requires review. -/
def ProjectStats.reviewBurden (s : ProjectStats) : Nat :=
  s.mainTheorem.lineCount

instance : ToJson ProjectStats where
  toJson s := Json.mkObj [
    ("main_theorem", toJson s.mainTheorem),
    ("proof_of_main_theorem", toJson s.proofOfMainTheorem),
    ("total_lines", toJson s.totalLines),
    ("review_burden", toJson s.reviewBurden)
  ]

/-! ## Verification Report -/

/-- Complete verification report -/
structure VerificationReport where
  /-- Project name/prefix -/
  projectName : String
  /-- Results of all checks -/
  checks : List CheckResult
  /-- Line count statistics -/
  stats : ProjectStats
  /-- Whether all checks passed -/
  allPassed : Bool
  deriving Inhabited, Repr

instance : ToJson VerificationReport where
  toJson r := Json.mkObj [
    ("project", toJson r.projectName),
    ("checks", toJson r.checks),
    ("stats", toJson r.stats),
    ("all_passed", toJson r.allPassed)
  ]

end TAIL
