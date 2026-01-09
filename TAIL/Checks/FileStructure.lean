/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# TAIL Checks - File Structure

Checks for project structure:
- Structure check (required declarations exist)
-/

namespace TAIL.Checks

open Lean

/-! ## Structure Check -/

/-- Verify that required declarations exist:
    - `{projectPrefix}.StatementOfTheorem` exists and is a def
    - `{projectPrefix}.mainTheorem` exists in ProofOfMainTheorem module

    Note: In the olean format, theorems imported from other modules appear as axioms.
    This is normal behavior of the Lean module system. -/
def checkStructure (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let statementName := resolved.statementName'
  let theoremName := resolved.theoremName'
  let mainModule := resolved.mainTheoremModule
  let proofModule := resolved.proofOfMainTheoremModule

  -- Find MainTheorem module
  let some mainMod := findModule modules mainModule
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check StatementOfTheorem exists and is a def
  let some statementDecl := findDecl mainMod statementName
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"'{statementName}' not found in MainTheorem module"
        [s!"Expected declaration at fully qualified name: {statementName}"]

  if !statementDecl.kind.isDef then
    return CheckResult.fail CheckCategory.structure "Structure"
      s!"'{statementName}' is a {statementDecl.kind}, expected def"
      ["StatementOfTheorem must be a definition, not a theorem"]

  -- Find ProofOfMainTheorem module
  let some proofMod := findModule modules proofModule
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check mainTheorem exists
  -- Note: In olean, theorems may appear as axioms due to module system
  let some theoremDecl := findDecl proofMod theoremName
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"'{theoremName}' not found in ProofOfMainTheorem module"
        [s!"Expected theorem at fully qualified name: {theoremName}"]

  -- Accept both theorem and axiom kinds (module system causes theorems to appear as axioms)
  if !theoremDecl.kind.isTheorem && theoremDecl.kind != .ax then
    return CheckResult.fail CheckCategory.structure "Structure"
      s!"'{theoremName}' is a {theoremDecl.kind}, expected theorem"
      ["mainTheorem must be a theorem"]

  return CheckResult.pass CheckCategory.structure "Structure"
    s!"Verified: {statementName} (def), {theoremName} (theorem)"

end TAIL.Checks
