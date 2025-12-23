/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# TAIL Checks - Imports

Checks for import discipline:
- MainTheorem.lean imports (Mathlib only in strict mode, + Definitions/ in default mode)
- ProofOfMainTheorem.lean imports (must include MainTheorem and standard library)
-/

namespace TAIL.Checks

open Lean

/-! ## 5. Imports Check -/

/-- Check MainTheorem.lean imports -/
def checkMainTheoremImports (mainMod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut violations : Array String := #[]

  for imp in mainMod.imports do
    let modName := imp.module
    let modStr := modName.toString

    -- Check if this is a project import
    if modStr.startsWith resolved.projectPrefix then
      -- In default mode, Definitions/ imports are allowed
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      else
        violations := violations.push s!"  - {modStr} (project import not allowed)"
    else if !TAIL.isStandardLibraryImport modName then
      violations := violations.push s!"  - {modStr} (non-Mathlib import)"

  (violations, violations.isEmpty)

/-- Check ProofOfMainTheorem.lean imports -/
def checkProofImports (proofMod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut hasMainTheoremImport := false
  let mut hasStandardLibrary := false
  let mut violations : Array String := #[]

  for imp in proofMod.imports do
    let modName := imp.module
    let modStr := modName.toString

    if modName == resolved.mainTheoremModule then
      hasMainTheoremImport := true
    else if TAIL.isStandardLibraryImport modName then
      hasStandardLibrary := true
    else if modStr.startsWith resolved.projectPrefix then
      -- Definitions/ imports allowed in default mode
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      -- Proofs/ imports always allowed
      else if resolved.isProofsModule modName then
        continue
      else
        violations := violations.push s!"  - Unexpected project import: {modStr}"

  if !hasMainTheoremImport then
    violations := #[s!"  - Missing required import: MainTheorem"] ++ violations

  if !hasStandardLibrary then
    violations := #[s!"  - Missing standard library import (typically Mathlib)"] ++ violations

  (violations, violations.isEmpty)

/-- Check imports for MainTheorem.lean and ProofOfMainTheorem.lean -/
def checkImports (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let mainModule := resolved.mainTheoremModule
  let proofModule := resolved.proofOfMainTheoremModule

  let some mainMod := findModule modules mainModule
    | return CheckResult.fail CheckCategory.imports "Import Discipline"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  let some proofMod := findModule modules proofModule
    | return CheckResult.fail CheckCategory.imports "Import Discipline"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  let mut allViolations : Array String := #[]

  -- Check MainTheorem imports
  let (mainViolations, mainOk) := checkMainTheoremImports mainMod resolved
  if !mainOk then
    allViolations := allViolations.push "MainTheorem.lean import violations:"
    allViolations := allViolations ++ mainViolations

  -- Check ProofOfMainTheorem imports
  let (proofViolations, proofOk) := checkProofImports proofMod resolved
  if !proofOk then
    allViolations := allViolations.push "ProofOfMainTheorem.lean import violations:"
    allViolations := allViolations ++ proofViolations

  if allViolations.isEmpty then
    let modeNote := if resolved.mode == .strict
      then "Mathlib-only imports verified"
      else "Mathlib/Definitions imports verified"
    return CheckResult.pass CheckCategory.imports "Import Discipline" modeNote
  else
    return CheckResult.fail CheckCategory.imports "Import Discipline"
      "Import violations detected" allViolations.toList

end TAIL.Checks
