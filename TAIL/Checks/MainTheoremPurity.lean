/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# MainTheorem Purity Check

Verify MainTheorem.lean contains no lemmas or theorems (only defs).
Uses environment introspection instead of text-based parsing.
-/

namespace TAIL.Checks

open Lean Meta

/-- Check that MainTheorem.lean contains only allowed declarations -/
def checkMainTheoremPurity (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let mainModule := resolved.mainTheoremModule

  -- Get all declarations in the MainTheorem module
  let decls := TAIL.getModuleDeclarations env mainModule

  -- Find theorems (which are forbidden in MainTheorem.lean)
  let theorems := decls.filter fun name =>
    if TAIL.isInternalName name then false
    else match env.find? name with
      | some (.thmInfo _) => true
      | _ => false

  -- Check that the statement definition exists
  let statementName := resolved.statementName'
  let hasStatement := decls.any (· == statementName)

  let mut details : List String := []
  let mut passed := true

  -- Check for forbidden theorem declarations
  if !theorems.isEmpty then
    passed := false
    for thm in theorems do
      details := details ++ [s!"theorem {thm}"]

  -- Check that StatementOfTheorem exists
  if !hasStatement then
    passed := false
    details := details ++ [s!"'{statementName}' not found"]

  if passed then
    let declCount := decls.filter (!TAIL.isInternalName ·) |>.length
    return CheckResult.pass "MainTheorem Purity"
      s!"Contains {declCount} allowed declarations"
  else
    return CheckResult.fail "MainTheorem Purity"
      "MainTheorem.lean contains disallowed declarations" details

end TAIL.Checks
