/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# Statement Purity Check

Verify MainTheorem.lean contains only allowed declarations:
- In strict mode: only StatementOfTheorem
- In default mode: StatementOfTheorem (extra defs trigger warning to move to Definitions/)

Theorems are never allowed in MainTheorem.lean.
Uses environment introspection instead of text-based parsing.
-/

namespace TAIL.Checks

open Lean Meta

/-- Check that MainTheorem.lean contains only allowed declarations -/
def checkStatementPurity (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let mainModule := resolved.mainTheoremModule

  -- Get all declarations in the MainTheorem module
  let decls := TAIL.getModuleDeclarations env mainModule
  let userDecls := decls.filter (!TAIL.isInternalName ·)

  -- Find theorems (which are forbidden in MainTheorem.lean)
  let theorems := userDecls.filter fun name =>
    match env.find? name with
    | some (.thmInfo _) => true
    | _ => false

  -- Check that the statement definition exists
  let statementName := resolved.statementName'
  let hasStatement := userDecls.any (· == statementName)

  -- Find extra definitions (not StatementOfTheorem)
  let extraDefs := userDecls.filter fun name =>
    name != statementName && match env.find? name with
    | some (.thmInfo _) => false  -- Already counted in theorems
    | _ => true

  let mut details : List String := []
  let mut passed := true

  -- Check for forbidden theorem declarations (error in both modes)
  if !theorems.isEmpty then
    passed := false
    for thm in theorems do
      details := details ++ [s!"ERROR: theorem {thm} (theorems not allowed)"]

  -- Check that StatementOfTheorem exists
  if !hasStatement then
    passed := false
    details := details ++ [s!"ERROR: '{statementName}' not found"]

  -- Handle extra definitions based on mode
  if !extraDefs.isEmpty then
    match resolved.mode with
    | .strict =>
      -- Strict mode: extra defs are an error
      passed := false
      for def_ in extraDefs do
        details := details ++ [s!"ERROR: {def_} (strict mode allows only StatementOfTheorem)"]
    | .default =>
      -- Default mode: extra defs are a warning
      for def_ in extraDefs do
        details := details ++ [s!"WARNING: {def_} (consider moving to Definitions/ folder)"]

  if passed then
    if extraDefs.isEmpty then
      return CheckResult.pass "Statement Purity"
        s!"MainTheorem.lean contains only StatementOfTheorem"
    else
      return CheckResult.pass "Statement Purity"
        s!"MainTheorem.lean valid ({extraDefs.length} extra defs - consider moving to Definitions/)"
  else
    return CheckResult.fail "Statement Purity"
      "MainTheorem.lean contains disallowed declarations" details

/-- Alias for backwards compatibility -/
def checkMainTheoremPurity := checkStatementPurity

end TAIL.Checks
