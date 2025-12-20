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
# Proofs Purity Check

Verify that files in the Proofs/ folder:
- Do not contain axioms
- Do not contain opaque declarations
- Do not use sorry

This check runs in both modes when a Proofs/ folder exists.
-/

namespace TAIL.Checks

open Lean Meta

/-- Check declarations in a Proofs/ module -/
def checkProofsModuleDeclarations (env : Environment) (moduleName : Name) :
    List String × Bool :=
  let decls := TAIL.getModuleDeclarations env moduleName
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

/-- Check if a declaration uses sorry by checking axiom dependencies -/
private def usagesSorry (env : Environment) (declName : Name) : MetaM Bool := do
  -- Get all axioms this declaration depends on
  try
    let mut visited : Std.HashSet Name := {}
    let mut toVisit : Array Name := #[declName]

    while h : toVisit.size > 0 do
      let curr := toVisit[toVisit.size - 1]'(by omega)
      toVisit := toVisit.pop

      if visited.contains curr then continue
      visited := visited.insert curr

      let some currInfo := env.find? curr | continue

      match currInfo with
      | .axiomInfo _ =>
        if curr == ``sorryAx then return true
      | .defnInfo val =>
        let deps := val.value.getUsedConstants
        toVisit := toVisit ++ deps.filter (!visited.contains ·)
      | .thmInfo val =>
        let deps := val.value.getUsedConstants
        toVisit := toVisit ++ deps.filter (!visited.contains ·)
      | _ => continue

    return false
  catch _ =>
    return false

/-- Check that all Proofs/ files follow the rules -/
def checkProofsPurity (resolved : ResolvedConfig) : MetaM CheckResult := do
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

  let mut allViolations : List String := []
  let mut moduleCount := 0
  let mut sorryUsages : List (Name × Name) := []  -- (module, declaration)

  for modName in proofsModules do
    moduleCount := moduleCount + 1

    -- Check declarations for axioms/opaques
    let (declViolations, declsOk) := checkProofsModuleDeclarations env modName
    if !declsOk then
      allViolations := allViolations ++ [s!"Declaration violations in {modName}:"] ++ declViolations

    -- Check for sorry usage in this module
    let moduleDecls := TAIL.getModuleDeclarations env modName
    let userDecls := moduleDecls.filter (!TAIL.isInternalName ·)

    for decl in userDecls do
      let usesSorry ← usagesSorry env decl
      if usesSorry then
        sorryUsages := (modName, decl) :: sorryUsages

  -- Add sorry violations
  if !sorryUsages.isEmpty then
    allViolations := allViolations ++ ["Sorry usage in Proofs/:"]
    for (modName, decl) in sorryUsages do
      allViolations := allViolations ++ [s!"  - {decl} in {modName}"]

  if allViolations.isEmpty then
    return CheckResult.pass "Proofs Purity"
      s!"All {moduleCount} Proofs/ modules are valid"
  else
    return CheckResult.fail "Proofs Purity"
      "Proofs/ folder contains disallowed content" allViolations

end TAIL.Checks
