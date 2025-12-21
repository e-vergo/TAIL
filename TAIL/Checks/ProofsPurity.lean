/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment
import TAIL.Checks.Structure
import TAIL.Utils

/-!
# Proofs Purity Check

Verify that files in the Proofs/ folder:
- Do not contain axioms
- Do not contain opaque declarations
- Do not use sorry
- Import only from allowed sources (Mathlib, Definitions/, other Proofs/)
- Do NOT import from MainTheorem or ProofOfMainTheorem

This check runs in both modes when a Proofs/ folder exists.
-/

namespace TAIL.Checks

open Lean Meta

/-- Check imports for a Proofs/ module.

    Allowed imports:
    - Standard libraries (Mathlib, Lean, etc.)
    - Definitions/ modules (default mode only)
    - Other Proofs/ modules

    Disallowed imports:
    - MainTheorem
    - ProofOfMainTheorem
-/
def checkProofsModuleImports (env : Environment) (moduleName : Name) (resolved : ResolvedConfig) :
    List String × Bool := Id.run do
  let some imports := TAIL.getModuleImports env moduleName
    | ([], true)  -- If we can't get imports, assume OK (shouldn't happen)

  let mut violations : List String := []

  for imp in imports do
    let modName := imp.module
    let modStr := modName.toString

    -- Check for disallowed project imports
    if modName == resolved.mainTheoremModule then
      violations := violations ++ [s!"  - Cannot import MainTheorem from Proofs/"]
    else if modName == resolved.proofOfMainTheoremModule then
      violations := violations ++ [s!"  - Cannot import ProofOfMainTheorem from Proofs/"]
    -- Allow standard library
    else if TAIL.isStandardLibraryImport modName then
      continue
    -- Check other project imports
    else if modStr.startsWith resolved.projectPrefix then
      -- Definitions/ imports allowed in default mode
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      -- Other Proofs/ modules always allowed
      else if resolved.isProofsModule modName then
        continue
      else
        -- Some other project import that's not allowed
        violations := violations ++ [s!"  - Unexpected project import: {modStr}"]

  (violations, violations.isEmpty)

/-- Check declarations in a Proofs/ module -/
def checkProofsModuleDeclarations (env : Environment) (moduleName : Name)
    (index : Option TAIL.EnvironmentIndex := none) : List String × Bool :=
  let decls := TAIL.getModuleDeclarations env moduleName index
  let userDecls := decls.filter (!TAIL.isInternalName ·)

  let violations := userDecls.filterMap fun decl =>
    match env.find? decl with
    | some (.axiomInfo _) =>
      -- sorryAx will be caught by the soundness check
      if decl == ``sorryAx then none
      else some s!"  - axiom {decl} (axioms not allowed in Proofs/)"
    | some (.opaqueInfo _) =>
      some s!"  - opaque {decl} (opaque not allowed in Proofs/)"
    | _ => none

  (violations, violations.isEmpty)

/-- Check that all Proofs/ files follow the rules -/
def checkProofsPurity (resolved : ResolvedConfig) (index : Option TAIL.EnvironmentIndex := none) : MetaM CheckResult := do
  -- Skip if no Proofs/ folder
  if resolved.proofsPath.isNone then
    return CheckResult.pass "Proofs Purity"
      "Skipped (no Proofs/ folder present)"

  let env ← getEnv

  -- Find all modules that are in Proofs/
  let allModules := env.header.moduleNames
  let proofsModules := allModules.filter fun name =>
    resolved.isProofsModule name

  if proofsModules.isEmpty then
    return CheckResult.pass "Proofs Purity"
      "No modules found in Proofs/ folder"

  let mut allViolationsArray : Array String := #[]
  let mut moduleCount := 0
  let mut sorryUsages : List (Name × Name) := []  -- (module, declaration)

  for modName in proofsModules do
    moduleCount := moduleCount + 1

    -- Check 1: Import restrictions
    let (importViolations, importsOk) := checkProofsModuleImports env modName resolved
    if !importsOk then
      allViolationsArray := allViolationsArray.push s!"Import violations in {modName}:"
      allViolationsArray := allViolationsArray ++ importViolations.toArray

    -- Check 2: Declaration restrictions (axioms/opaques)
    let (declViolations, declsOk) := checkProofsModuleDeclarations env modName index
    if !declsOk then
      allViolationsArray := allViolationsArray.push s!"Declaration violations in {modName}:"
      allViolationsArray := allViolationsArray ++ declViolations.toArray

    -- Check 3: Sorry usage
    let moduleDecls := TAIL.getModuleDeclarations env modName index
    let userDecls := moduleDecls.filter (!TAIL.isInternalName ·)

    for decl in userDecls do
      let usesSorry ← TAIL.usagesSorry env decl
      if usesSorry then
        sorryUsages := (modName, decl) :: sorryUsages

  -- Add sorry violations
  if !sorryUsages.isEmpty then
    allViolationsArray := allViolationsArray.push "Sorry usage in Proofs/:"
    for (modName, decl) in sorryUsages do
      allViolationsArray := allViolationsArray.push s!"  - {decl} in {modName}"

  if allViolationsArray.isEmpty then
    return CheckResult.pass "Proofs Purity"
      s!"All {moduleCount} Proofs/ modules are valid"
  else
    return CheckResult.fail "Proofs Purity"
      "Proofs/ folder contains disallowed content" allViolationsArray.toList

end TAIL.Checks
