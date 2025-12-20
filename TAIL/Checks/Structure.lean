/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# Structure Check

Verify that required declarations exist with correct types:
- `StatementOfTheorem : Prop`
- `mainTheorem : StatementOfTheorem`
- MainTheorem.lean imports only from Mathlib (no project imports)

This is the core semantic verification per the TAIL Standard.
-/

namespace TAIL.Checks

open Lean Meta

/-! ## Import Verification -/

/-- Allowed import prefixes for MainTheorem.lean (TAIL Standard) -/
def allowedImportPrefixes : List String :=
  ["Mathlib", "Init", "Std", "Lean", "Qq", "Aesop", "ProofWidgets", "Batteries"]

/-- Check if an import is from an allowed source -/
def isAllowedImport (moduleName : Name) : Bool :=
  let nameStr := moduleName.toString
  allowedImportPrefixes.any (nameStr.startsWith ·)

/-- Get imports for a specific module from the environment -/
def getModuleImports (env : Environment) (moduleName : Name) : Option (Array Import) := do
  let idx ← env.getModuleIdx? moduleName
  let moduleData := env.header.moduleData[idx.toNat]?
  return moduleData.map (·.imports) |>.getD #[]

/-- Check that MainTheorem.lean only imports from allowed sources.
    In strict mode: only Mathlib allowed
    In default mode: Mathlib and Definitions/ folder allowed -/
def checkMainTheoremImports (env : Environment) (mainModule : Name) (resolved : ResolvedConfig) :
    List String × Bool := Id.run do
  let some imports := getModuleImports env mainModule
    | (["Could not retrieve imports for MainTheorem module"], false)

  let mut violations : List String := []

  for imp in imports do
    let modName := imp.module
    let modStr := modName.toString

    -- Check if this is a project import
    if modStr.startsWith resolved.projectPrefix then
      -- In default mode, Definitions/ imports are allowed
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        -- This is fine - Definitions/ imports are allowed in default mode
        continue
      else
        -- Project import not from Definitions/ (or we're in strict mode)
        violations := violations ++ [s!"  - {modStr} (project import not allowed)"]
    else if !isAllowedImport modName then
      violations := violations ++ [s!"  - {modStr} (non-Mathlib import)"]

  (violations, violations.isEmpty)

/-! ## Type Verification -/

/-- Result of type verification -/
structure TypeVerificationResult where
  statementName : Name
  statementIsProp : Bool
  theoremName : Name
  theoremTypeMatches : Bool
  equalityMethod : String  -- "syntactic" or "definitional"
  deriving Repr

/-- Verify that StatementOfTheorem : Prop and mainTheorem : StatementOfTheorem -/
def checkStructure (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let statementName := resolved.statementName'
  let theoremName := resolved.theoremName'
  let mainModule := resolved.mainTheoremModule

  let mut details : List String := []

  -- Check 0: MainTheorem.lean imports only from allowed sources
  let (importViolations, importsOk) := checkMainTheoremImports env mainModule resolved
  if !importsOk then
    let modeNote := if resolved.mode == .strict
      then "In strict mode, MainTheorem.lean must only import from Mathlib"
      else "MainTheorem.lean can only import from Mathlib or Definitions/"
    return CheckResult.fail "Structure"
      "MainTheorem.lean has disallowed imports (TAIL Standard violation)"
      ([modeNote] ++ importViolations)

  let importMsg := if resolved.mode == .strict
    then "MainTheorem.lean imports only from Mathlib"
    else "MainTheorem.lean imports only from Mathlib/Definitions"
  details := details ++ [importMsg]

  -- Check 1: StatementOfTheorem exists
  let statementInfo ← match env.find? statementName with
    | some info => pure info
    | none =>
      return CheckResult.fail "Structure"
        s!"'{statementName}' not found" []

  -- Check 2: StatementOfTheorem : Prop
  -- The type of a definition `def X : Prop := ...` is Prop
  -- But we need to check if the *type* of the constant is Prop
  let statementType := statementInfo.type

  -- First check syntactically
  let isPropSyntactic := TAIL.isPropSyntactic statementType

  -- Then check definitionally if needed
  let (statementIsProp, equalityMethod) ← do
    if isPropSyntactic then
      pure (true, "syntactic")
    else
      let isPropDef ← TAIL.isPropDefEq statementType
      pure (isPropDef, "definitional")

  if !statementIsProp then
    -- Pretty print the type for error message
    let typeStr ← Meta.ppExpr statementType
    return CheckResult.fail "Structure"
      s!"'{statementName}' has type '{typeStr}', expected 'Prop'"
      [s!"The statement definition must have type Prop"]

  details := details ++ [s!"{statementName} : Prop [verified {equalityMethod}]"]

  -- Check 3: mainTheorem exists and is a theorem
  let theoremInfo ← match env.find? theoremName with
    | some (.thmInfo tinfo) => pure tinfo
    | some info =>
      let kind := TAIL.getDeclKind info
      return CheckResult.fail "Structure"
        s!"'{theoremName}' exists but is a {kind}, not a theorem" []
    | none =>
      return CheckResult.fail "Structure"
        s!"'{theoremName}' not found" []

  -- Check 4: mainTheorem : StatementOfTheorem
  -- The type of the theorem should be exactly the statement
  let expectedType := mkConst statementName
  let actualType := theoremInfo.type

  -- First try syntactic equality
  let syntacticMatch := actualType.equal expectedType

  let (theoremTypeMatches, typeEqMethod) ← do
    if syntacticMatch then
      pure (true, "syntactic")
    else
      -- Try definitional equality
      let defEqMatch ← isDefEq actualType expectedType
      pure (defEqMatch, "definitional")

  if !theoremTypeMatches then
    let actualStr ← Meta.ppExpr actualType
    let expectedStr ← Meta.ppExpr expectedType
    return CheckResult.fail "Structure"
      s!"'{theoremName}' has type '{actualStr}', expected '{expectedStr}'"
      [s!"The main theorem must prove exactly the statement definition"]

  details := details ++ [s!"{theoremName} : {statementName} [verified {typeEqMethod}]"]

  -- All checks passed
  return CheckResult.pass "Structure"
    s!"Verified: {statementName} : Prop, {theoremName} : {statementName}"

end TAIL.Checks
