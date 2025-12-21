/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment
import TAIL.Utils

/-!
# Import Discipline Check (Environment-Based)

Verify imports follow the strict TAIL Standard using environment introspection.

**MainTheorem.lean**: Checked in Structure.lean
- Can ONLY import Mathlib, Init, Lean, Batteries, etc.

**ProofOfMainTheorem.lean**:
- MUST import MainTheorem (to access StatementOfTheorem)
- MUST import from Mathlib (standard library)
- CAN import from Definitions/ (default mode only)
- CAN import from Proofs/ (helper lemmas)
- Only StatementOfTheorem and mainTheorem should be re-exported (verified via re-import test)

Note: Lean 4.27+ module system doesn't expose `public` vs `import` distinction in the
environment API. We verify the EFFECT (what's visible) rather than the syntax.
-/

namespace TAIL.Checks

open Lean

/-- Verify ProofOfMainTheorem.lean has appropriate imports per TAIL Standard.

    Required imports:
    - MainTheorem (to access StatementOfTheorem)
    - At least one standard library (typically Mathlib)

    Optional imports (depending on mode):
    - Definitions/ modules (default mode only)
    - Proofs/ modules (always allowed)
-/
def checkProofOfMainTheoremImports (env : Environment) (resolved : ResolvedConfig) :
    List String × Bool := Id.run do
  let proofModule := resolved.proofOfMainTheoremModule

  let some imports := TAIL.getModuleImports env proofModule
    | (["Could not retrieve imports for ProofOfMainTheorem module"], false)

  let mut hasMainTheoremImport := false
  let mut hasStandardLibrary := false
  let mut violations : List String := []

  for imp in imports do
    let modName := imp.module
    let modStr := modName.toString

    -- Check if this imports MainTheorem
    if modName == resolved.mainTheoremModule then
      hasMainTheoremImport := true
    -- Check for standard library imports
    else if TAIL.isStandardLibraryImport modName then
      hasStandardLibrary := true
    -- Check project imports
    else if modStr.startsWith resolved.projectPrefix then
      -- Definitions/ imports allowed in default mode
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      -- Proofs/ imports always allowed
      else if resolved.isProofsModule modName then
        continue
      -- MainTheorem already handled above
      else if modName == resolved.mainTheoremModule then
        continue
      else
        -- Some other project import that's not allowed
        violations := violations ++ [s!"  - Unexpected project import: {modStr}"]

  -- Verify required imports are present
  if !hasMainTheoremImport then
    violations := ["  - Missing required import: MainTheorem.lean"] ++ violations

  if !hasStandardLibrary then
    violations := ["  - Missing standard library import (typically Mathlib)"] ++ violations

  (violations, violations.isEmpty)

/-- Check imports using environment introspection.

    This performs two checks:
    1. Direct import verification: ProofOfMainTheorem imports the right modules
    2. Re-import test: Only allowed declarations are visible to downstream importers
-/
def checkImports (resolved : ResolvedConfig) (index : Option TAIL.EnvironmentIndex := none) : MetaM CheckResult := do
  let env ← getEnv

  -- Check 1: Verify ProofOfMainTheorem imports
  let (importViolations, importsOk) := checkProofOfMainTheoremImports env resolved
  if !importsOk then
    return CheckResult.fail "Import Discipline"
      "ProofOfMainTheorem.lean has incorrect imports (TAIL Standard violation)"
      (["Per TAIL Standard, ProofOfMainTheorem.lean must import MainTheorem and standard libraries"] ++ importViolations)

  -- Check 2: Verify module visibility using the re-import test
  -- This ensures only StatementOfTheorem and mainTheorem are re-exported
  let visibilityResult := checkModuleVisibility env
    resolved.projectPrefix
    resolved.statementName'
    resolved.theoremName'
    resolved.mode
    index

  return visibilityResult

end TAIL.Checks
