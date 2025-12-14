/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# Proof Minimality Check

Verify ProofOfMainTheorem.lean contains exactly one theorem (the main theorem).
Uses environment introspection instead of text-based parsing.
-/

namespace TAIL.Checks

open Lean Meta

/-- Verify proof file contains exactly one theorem -/
def checkProofMinimality (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let proofModule := resolved.proofOfMainTheoremModule

  -- Get all declarations in the ProofOfMainTheorem module
  let decls := TAIL.getModuleDeclarations env proofModule

  -- Filter to theorems only (exclude internal/auxiliary)
  let theorems := decls.filter fun name =>
    match env.find? name with
    | some (.thmInfo _) => !TAIL.isInternalName name
    | _ => false

  -- Filter to non-theorem declarations (potential violations)
  let nonTheorems := decls.filter fun name =>
    if TAIL.isInternalName name then false
    else match env.find? name with
      | some (.thmInfo _) => false
      | some (.defnInfo _) => true  -- defs are violations
      | some (.axiomInfo _) => true
      | some (.opaqueInfo _) => true
      | _ => false

  let mut details : List String := []
  let mut passed := true

  -- Check theorem count
  if theorems.length == 0 then
    passed := false
    details := details ++ ["No theorem found in ProofOfMainTheorem.lean"]
  else if theorems.length == 1 then
    let thm := theorems.head!
    let expectedName := resolved.theoremName'
    if thm != expectedName then
      details := details ++ [s!"Found theorem '{thm}' (expected '{expectedName}')"]
      -- This is a warning, not a failure
  else
    passed := false
    details := details ++ [s!"Multiple theorems found ({theorems.length}):"]
    for thm in theorems do
      details := details ++ [s!"  - {thm}"]

  -- Check for non-theorem declarations
  if !nonTheorems.isEmpty then
    passed := false
    details := details ++ [s!"Extra declarations found ({nonTheorems.length}):"]
    for decl in nonTheorems do
      let kind := match env.find? decl with
        | some info => TAIL.getDeclKind info
        | none => "unknown"
      details := details ++ [s!"  - {kind} {decl}"]

  if passed then
    let thmName := if theorems.isEmpty then "none" else theorems.head!.toString
    return CheckResult.pass "Proof Minimality"
      s!"Contains exactly one theorem: {thmName}"
  else
    return CheckResult.fail "Proof Minimality"
      "ProofOfMainTheorem.lean structure invalid" details

end TAIL.Checks
