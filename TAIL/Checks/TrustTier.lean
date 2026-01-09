/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# TAIL Checks - Trust Tier

Enforces trust tier rules: the machine-verified tier (ProofOfMainTheorem.lean + Proofs/)
can only contain Prop-valued declarations.
-/

namespace TAIL.Checks

open Lean

/-! ## Trust Tier Check -/

/-- Check that machine-verified tier contains only Prop-valued declarations.
    The machine-verified tier consists of:
    - ProofOfMainTheorem.lean
    - All modules in Proofs/

    Rules:
    - Theorems are always allowed (inherently Prop-valued)
    - Structures/inductives are rejected (.ind, .ctor, .recr kinds)
    - Definitions must return Prop (checked via returnsProp)
    - Auto-generated declarations are skipped -/
def checkTrustTier (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  -- Collect modules in the machine-verified tier
  let machineVerifiedModules := modules.filter fun mod =>
    mod.name == resolved.proofOfMainTheoremModule || resolved.isProofsModule mod.name

  if machineVerifiedModules.isEmpty then
    return CheckResult.pass CheckCategory.trustTier "Trust Tier"
      "No machine-verified modules found"

  let mut allViolations : Array String := #[]
  let mut declCount := 0

  for mod in machineVerifiedModules do
    let userDecls := getUserDeclarations mod

    for decl in userDecls do
      -- Skip auto-generated declarations
      if shouldSkipDeclaration decl.name then continue

      declCount := declCount + 1

      -- Theorems are always Prop-valued, allow them
      if decl.kind.isTheorem then continue

      -- Structures/inductives are not allowed in machine-verified tier
      if decl.kind == .ind then
        allViolations := allViolations.push
          s!"  - {mod.name}: inductive {decl.name} (structures/inductives not allowed in machine-verified tier)"
        continue

      if decl.kind == .ctor then
        allViolations := allViolations.push
          s!"  - {mod.name}: constructor {decl.name} (structures/inductives not allowed in machine-verified tier)"
        continue

      if decl.kind == .recr then
        allViolations := allViolations.push
          s!"  - {mod.name}: recursor {decl.name} (structures/inductives not allowed in machine-verified tier)"
        continue

      -- For definitions, check if they return Prop
      if decl.kind.isDef then
        if !returnsProp decl.type then
          allViolations := allViolations.push
            s!"  - {mod.name}: def {decl.name} does not return Prop (only Prop-valued definitions allowed)"

  if allViolations.isEmpty then
    return CheckResult.pass CheckCategory.trustTier "Trust Tier"
      s!"All {declCount} declarations in machine-verified tier are Prop-valued"
  else
    return CheckResult.fail CheckCategory.trustTier "Trust Tier"
      "Machine-verified tier contains non-Prop declarations" allViolations.toList

/-! ## Definitions Semantic Risks Check (Warnings Only) -/

/-- Patterns that could affect how MainTheorem.lean is interpreted. -/
private def semanticRiskPatterns : List (String × String) :=
  [ ("notation", "custom notation")
  , ("scoped notation", "scoped notation")
  , ("macro ", "macro definition")
  , ("macro_rules", "macro rules")
  , ("syntax ", "syntax declaration")
  , ("instance", "instance (check for Coe)")
  ]

/-- Check if a line contains a semantic risk pattern.
    Returns (hasRisk, patternName) if found. -/
private def hasSemanticRisk (line : String) : Option String := Id.run do
  let trimmed := line.trim
  -- Skip comments
  if trimmed.startsWith "--" then return none
  -- Skip lines inside doc comments
  if trimmed.startsWith "/-" then return none

  for (pattern, name) in semanticRiskPatterns do
    if trimmed.startsWith pattern then
      -- Special case: "instance" should only warn if it's a Coe instance
      if pattern == "instance" then
        if trimmed.containsSubstr "Coe" || trimmed.containsSubstr "CoeT" ||
           trimmed.containsSubstr "CoeTC" || trimmed.containsSubstr "CoeFun" then
          return some "coercion instance"
        else
          continue
      return some name
  return none

/-- Scan Definitions/ folder for semantic risk patterns.
    These are WARNINGS, not errors - they prompt extra human review. -/
def checkDefinitionsSemanticRisks (resolved : ResolvedConfig) : IO (Array String) := do
  -- Skip if strict mode or no Definitions/ folder
  if resolved.mode == .strict then return #[]
  let some defPath := resolved.definitionsPath | return #[]

  let leanFiles ← TAIL.discoverLeanFiles defPath
  let mut warnings : Array String := #[]

  for filePath in leanFiles do
    let content ← IO.FS.readFile filePath
    let lines := content.splitOn "\n"
    let relPath := filePath.toString.replace (resolved.projectRoot.toString ++ "/") ""

    let mut lineNumber := 0
    let mut fileRisks : Array String := #[]

    for line in lines do
      lineNumber := lineNumber + 1
      if let some riskName := hasSemanticRisk line then
        fileRisks := fileRisks.push s!"{riskName} (line {lineNumber})"

    if !fileRisks.isEmpty then
      let risksStr := String.intercalate ", " fileRisks.toList
      warnings := warnings.push s!"  WARNING: {relPath} contains {risksStr} - verify MainTheorem.lean semantics"

  return warnings

end TAIL.Checks
