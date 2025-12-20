/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# MainTheorem Isolation Check

Verify MainTheorem.lean contains only allowed declarations per the TAIL Standard:
- In strict mode: ONLY StatementOfTheorem
- In default mode: StatementOfTheorem (extra defs warn to move to Definitions/)

Disallowed in both modes: theorem, axiom, opaque, abbrev, notation, instance

Uses environment introspection instead of text-based parsing.
-/

namespace TAIL.Checks

open Lean Meta

/-- Check that MainTheorem.lean contains only allowed declarations.

    Strict mode: ONLY StatementOfTheorem allowed
    Default mode: StatementOfTheorem + defs (with warning to move to Definitions/)

    Both modes disallow: theorem, axiom, opaque, abbrev, instance -/
def checkMainTheoremIsIsolated (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let mainModule := resolved.mainTheoremModule
  let statementName := resolved.statementName'

  -- Get all declarations in the MainTheorem module
  let decls := TAIL.getModuleDeclarations env mainModule
  let userDecls := decls.filter (!TAIL.isInternalName ·)

  let mut theorems : List Name := []
  let mut axioms : List Name := []
  let mut opaques : List Name := []
  let mut abbrevs : List Name := []
  let mut instances : List Name := []
  let mut extraDefs : List Name := []

  -- Categorize all declarations
  for name in userDecls do
    if name == statementName then continue  -- StatementOfTheorem is always allowed

    match env.find? name with
    | some (.thmInfo _) => theorems := name :: theorems
    | some (.axiomInfo _) => axioms := name :: axioms
    | some (.opaqueInfo _) => opaques := name :: opaques
    | some (.defnInfo info) =>
      -- Check if it's an abbrev
      if info.hints.isAbbrev then
        abbrevs := name :: abbrevs
      -- Check if it's an instance
      else if (← isInstance name) then
        instances := name :: instances
      else
        extraDefs := name :: extraDefs
    | some (.inductInfo _) =>
      -- Inductives/structures are treated as definitions in this context
      extraDefs := name :: extraDefs
    | _ => continue

  -- Note: notation is syntax-level and doesn't create constants, so we can't detect it via environment
  -- This is acceptable since notation in MainTheorem.lean should be in Definitions/ anyway

  let mut details : List String := []
  let mut passed := true
  let mut hasStatement := userDecls.any (· == statementName)

  -- Check that StatementOfTheorem exists
  if !hasStatement then
    passed := false
    details := details ++ [s!"ERROR: '{statementName}' not found"]

  -- Check for disallowed declarations (forbidden in both modes)
  if !theorems.isEmpty then
    passed := false
    for thm in theorems do
      details := details ++ [s!"ERROR: theorem {thm} (theorems not allowed in MainTheorem.lean)"]

  if !axioms.isEmpty then
    passed := false
    for ax in axioms do
      details := details ++ [s!"ERROR: axiom {ax} (axioms not allowed in MainTheorem.lean)"]

  if !opaques.isEmpty then
    passed := false
    for op in opaques do
      details := details ++ [s!"ERROR: opaque {op} (opaque not allowed in MainTheorem.lean)"]

  if !abbrevs.isEmpty then
    passed := false
    for ab in abbrevs do
      details := details ++ [s!"ERROR: abbrev {ab} (abbrev not allowed - use Definitions/ folder)"]

  if !instances.isEmpty then
    passed := false
    for inst in instances do
      details := details ++ [s!"ERROR: instance {inst} (instances not allowed - use Definitions/ folder)"]

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
      return CheckResult.pass "MainTheorem Isolation"
        s!"MainTheorem.lean contains only StatementOfTheorem"
    else
      return CheckResult.pass "MainTheorem Isolation"
        s!"MainTheorem.lean valid ({extraDefs.length} extra defs - consider moving to Definitions/)"
  else
    return CheckResult.fail "MainTheorem Isolation"
      "MainTheorem.lean contains disallowed declarations" details

end TAIL.Checks
