/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment
import TAIL.Checks.Structure

/-!
# Definitions Purity Check

Verify that files in the Definitions/ folder:
- Only import from Mathlib or other Definitions/ files (not Proofs/)
- Only contain definitions (def, abbrev, structure, inductive, class, instance)
- No theorems allowed
- No axioms/opaques allowed

This check only runs in default mode when a Definitions/ folder exists.
-/

namespace TAIL.Checks

open Lean Meta

/-- Allowed import prefixes for Definitions/ files -/
def definitionsAllowedImportPrefixes : List String :=
  ["Mathlib", "Init", "Std", "Lean", "Qq", "Aesop", "ProofWidgets", "Batteries"]

/-- Check imports for a Definitions/ module -/
def checkDefinitionsModuleImports (env : Environment) (moduleName : Name) (resolved : ResolvedConfig) :
    List String × Bool :=
  match getModuleImports env moduleName with
  | none => (["Could not retrieve imports"], false)
  | some imports =>
    let violations := imports.toList.filterMap fun imp =>
      let modName := imp.module
      let modStr := modName.toString
      -- Check if this is a project import
      if modStr.startsWith resolved.projectPrefix then
        -- Only Definitions/ imports are allowed from project
        if resolved.isDefinitionsModule modName then
          none  -- OK
        else
          some s!"  - {modStr} (only Definitions/ imports allowed)"
      else if !definitionsAllowedImportPrefixes.any (modStr.startsWith ·) then
        some s!"  - {modStr} (non-Mathlib import)"
      else
        none
    (violations, violations.isEmpty)

/-- Check declarations in a Definitions/ module -/
def checkDefinitionsModuleDeclarations (env : Environment) (moduleName : Name) :
    List String × Bool :=
  let decls := TAIL.getModuleDeclarations env moduleName
  let userDecls := decls.filter (!TAIL.isInternalName ·)

  let violations := userDecls.filterMap fun decl =>
    match env.find? decl with
    | some (.thmInfo _) =>
      some s!"  - theorem {decl} (theorems not allowed in Definitions/)"
    | some (.axiomInfo _) =>
      some s!"  - axiom {decl} (axioms not allowed)"
    | some (.opaqueInfo _) =>
      some s!"  - opaque {decl} (opaque not allowed)"
    | _ => none  -- def, inductInfo, ctorInfo, recInfo, quotInfo are fine

  (violations, violations.isEmpty)

/-- Check that all Definitions/ files follow the rules -/
def checkDefinitionsPurity (resolved : ResolvedConfig) : MetaM CheckResult := do
  -- Skip if no Definitions/ folder or in strict mode
  if resolved.mode == .strict then
    return CheckResult.pass "Definitions Purity"
      "Skipped (strict mode - no Definitions/ folder allowed)"

  if resolved.definitionsPath.isNone then
    return CheckResult.pass "Definitions Purity"
      "Skipped (no Definitions/ folder present)"

  let env ← getEnv

  -- Find all modules that are in Definitions/
  let allModules := env.header.moduleNames
  let defModules := allModules.filter fun name =>
    resolved.isDefinitionsModule name

  if defModules.isEmpty then
    return CheckResult.pass "Definitions Purity"
      "No modules found in Definitions/ folder"

  let mut allViolations : List String := []
  let mut moduleCount := 0

  for modName in defModules do
    moduleCount := moduleCount + 1

    -- Check imports
    let (importViolations, importsOk) := checkDefinitionsModuleImports env modName resolved
    if !importsOk then
      allViolations := allViolations ++ [s!"Import violations in {modName}:"] ++ importViolations

    -- Check declarations
    let (declViolations, declsOk) := checkDefinitionsModuleDeclarations env modName
    if !declsOk then
      allViolations := allViolations ++ [s!"Declaration violations in {modName}:"] ++ declViolations

  if allViolations.isEmpty then
    return CheckResult.pass "Definitions Purity"
      s!"All {moduleCount} Definitions/ modules are valid"
  else
    return CheckResult.fail "Definitions Purity"
      "Definitions/ folder contains disallowed content" allViolations

end TAIL.Checks
