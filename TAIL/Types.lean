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

/-! ## Verification Mode -/

/-- Verification modes for the Kim Morrison Standard.
    Strict enforces the original proposal; Default allows Definitions/ folder. -/
inductive VerificationMode where
  /-- Original Kim Morrison Standard: MainTheorem.lean contains only StatementOfTheorem -/
  | strict
  /-- Extended standard: allows Definitions/ folder for supporting types -/
  | default
  deriving DecidableEq, Repr, Inhabited

instance : ToString VerificationMode where
  toString
    | .strict => "strict"
    | .default => "default"

/-! ## Trust Levels -/

/-- Trust tiers for the Kim Morrison Standard.
    Files are classified as either requiring human review or machine-verified. -/
inductive TrustLevel where
  /-- Statement file: Mathlib-only imports, contains StatementOfTheorem def -/
  | MainTheorem
  /-- Definitions folder: supporting types/structures (default mode only, human review) -/
  | Definitions
  /-- Proof file: uses module system, exactly one public theorem -/
  | ProofOfMainTheorem
  /-- Proofs folder: helper lemmas (machine verified) -/
  | Proofs
  deriving DecidableEq, Repr, Inhabited

instance : ToString TrustLevel where
  toString
    | .MainTheorem => "MainTheorem"
    | .Definitions => "Definitions"
    | .ProofOfMainTheorem => "ProofOfMainTheorem"
    | .Proofs => "Proofs"

/-- Whether a trust level requires human review -/
def TrustLevel.requiresHumanReview : TrustLevel → Bool
  | .MainTheorem => true
  | .Definitions => true
  | .ProofOfMainTheorem => false
  | .Proofs => false

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

/-- Aggregated statistics for trust tiers -/
structure ProjectStats where
  mainTheorem : TierStats
  definitions : TierStats  -- Only used in default mode
  proofOfMainTheorem : TierStats
  proofs : TierStats  -- Helper lemmas folder
  deriving Inhabited, Repr

/-- Calculate total lines in the project -/
def ProjectStats.totalLines (s : ProjectStats) : Nat :=
  s.mainTheorem.lineCount +
  s.definitions.lineCount +
  s.proofOfMainTheorem.lineCount +
  s.proofs.lineCount

/-- Calculate review burden (lines requiring human review).
In default mode: MainTheorem.lean + Definitions/
In strict mode: MainTheorem.lean only (definitions will be empty) -/
def ProjectStats.reviewBurden (s : ProjectStats) : Nat :=
  s.mainTheorem.lineCount + s.definitions.lineCount

instance : ToJson ProjectStats where
  toJson s := Json.mkObj [
    ("main_theorem", toJson s.mainTheorem),
    ("definitions", toJson s.definitions),
    ("proof_of_main_theorem", toJson s.proofOfMainTheorem),
    ("proofs", toJson s.proofs),
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
