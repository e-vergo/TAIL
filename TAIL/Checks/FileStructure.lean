/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# TAIL Checks - File Structure

Checks for proper file organization:
- ProofOfMainTheorem Isolation (ProofOfMainTheorem contains exactly one theorem)
- MainTheorem Isolation (MainTheorem contains only allowed declarations)
-/

namespace TAIL.Checks

open Lean

/-! ## 3. ProofOfMainTheorem Isolation Check -/

/-- Verify ProofOfMainTheorem.lean contains exactly one theorem (the main theorem).
    Note: Due to the module system, theorems may appear as axioms in olean. -/
def checkProofOfMainTheoremIsolation (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let proofModule := resolved.proofOfMainTheoremModule
  let theoremName := resolved.theoremName'

  let some proofMod := findModule modules proofModule
    | return CheckResult.fail CheckCategory.contentRules "Proof Minimality"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  let userDecls := getUserDeclarations proofMod

  -- Filter to theorems/axioms (theorems appear as axioms in olean due to module system)
  let theoremsAndAxioms := userDecls.filter fun decl =>
    decl.kind.isTheorem || decl.kind == .ax

  -- Filter out standard axioms (propext, etc. shouldn't count)
  let projectTheorems := theoremsAndAxioms.filter fun decl =>
    !isStandardAxiom decl.name && decl.name != ``sorryAx

  let mut details : Array String := #[]
  let mut passed := true

  if projectTheorems.isEmpty then
    passed := false
    details := details.push "No theorem found in ProofOfMainTheorem.lean"
  else if projectTheorems.size == 1 then
    let thm := projectTheorems[0]!
    if thm.name != theoremName then
      details := details.push s!"Found theorem '{thm.name}' (expected '{theoremName}')"
      -- This is a warning, not a failure
  else
    passed := false
    details := details.push s!"Multiple theorems/axioms found ({projectTheorems.size}):"
    for thm in projectTheorems do
      details := details.push s!"  - {thm.kind} {thm.name}"

  -- Check for extra defs (potential violations)
  let extraDefs := userDecls.filter fun decl =>
    decl.kind.isDef

  if !extraDefs.isEmpty then
    passed := false
    details := details.push s!"Extra definitions found ({extraDefs.size}):"
    for def_ in extraDefs do
      details := details.push s!"  - def {def_.name}"

  if passed then
    let thmName := if projectTheorems.isEmpty then "none" else projectTheorems[0]!.name.toString
    return CheckResult.pass CheckCategory.contentRules "ProofOfMainTheorem Isolation"
      s!"Contains exactly one theorem: {thmName}"
  else
    return CheckResult.fail CheckCategory.contentRules "ProofOfMainTheorem Isolation"
      "ProofOfMainTheorem.lean structure invalid" details.toList

/-! ## 4. MainTheorem Isolation Check -/

/-- Check that MainTheorem.lean contains only allowed declarations.
    - Should have no theorems, only defs
    - In strict mode: extra defs (beyond StatementOfTheorem) are errors
    - In default mode: extra defs are warnings -/
def checkMainTheoremIsolation (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let mainModule := resolved.mainTheoremModule
  let statementName := resolved.statementName'

  let some mainMod := findModule modules mainModule
    | return CheckResult.fail CheckCategory.contentRules "MainTheorem Isolation"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  let userDecls := getUserDeclarations mainMod

  let mut theorems : Array Name := #[]
  let mut axioms : Array Name := #[]
  let mut opaques : Array Name := #[]
  let mut extraDefs : Array Name := #[]

  for decl in userDecls do
    if decl.name == statementName then continue  -- StatementOfTheorem is always allowed

    match decl.kind with
    | .thm => theorems := theorems.push decl.name
    | .ax =>
      -- Skip standard axioms
      if !isStandardAxiom decl.name && decl.name != ``sorryAx then
        axioms := axioms.push decl.name
    | .opaq => opaques := opaques.push decl.name
    | .defn => extraDefs := extraDefs.push decl.name
    | .ind => extraDefs := extraDefs.push decl.name  -- inductives/structures
    | _ => continue

  let mut details : Array String := #[]
  let mut passed := true

  -- Check that StatementOfTheorem exists
  let hasStatement := userDecls.any (·.name == statementName)
  if !hasStatement then
    passed := false
    details := details.push s!"ERROR: '{statementName}' not found"

  -- Theorems are always disallowed
  if !theorems.isEmpty then
    passed := false
    for thm in theorems do
      details := details.push s!"ERROR: theorem {thm} (theorems not allowed in MainTheorem.lean)"

  -- Axioms are always disallowed (except standard ones, already filtered)
  if !axioms.isEmpty then
    passed := false
    for ax in axioms do
      details := details.push s!"ERROR: axiom {ax} (axioms not allowed in MainTheorem.lean)"

  -- Opaques are always disallowed
  if !opaques.isEmpty then
    passed := false
    for op in opaques do
      details := details.push s!"ERROR: opaque {op} (opaque not allowed in MainTheorem.lean)"

  -- Handle extra definitions based on mode
  if !extraDefs.isEmpty then
    match resolved.mode with
    | .strict =>
      passed := false
      for def_ in extraDefs do
        details := details.push s!"ERROR: {def_} (strict mode allows only StatementOfTheorem)"
    | .default =>
      for def_ in extraDefs do
        details := details.push s!"WARNING: {def_} (consider moving to Definitions/ folder)"

  if passed then
    if extraDefs.isEmpty then
      return CheckResult.pass CheckCategory.contentRules "MainTheorem Isolation"
        "MainTheorem.lean contains only StatementOfTheorem"
    else
      return CheckResult.pass CheckCategory.contentRules "MainTheorem Isolation"
        s!"MainTheorem.lean valid ({extraDefs.size} extra defs - consider moving to Definitions/)"
  else
    return CheckResult.fail CheckCategory.contentRules "MainTheorem Isolation"
      "MainTheorem.lean contains disallowed declarations" details.toList

end TAIL.Checks
