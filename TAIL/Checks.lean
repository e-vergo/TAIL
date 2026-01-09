/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers
import TAIL.Checks.FileStructure
import TAIL.Checks.Imports
import TAIL.Checks.SafeVerify
import TAIL.Checks.TrustTier

/-!
# TAIL Checks

Verification checks using OleanReader instead of full environment loading.
This module re-exports all check functions from submodules and provides
the main `runChecks` orchestrator.

## Checks

1. **Structure** - Required declarations exist (MainTheorem.lean, ProofOfMainTheorem.lean)
2. **TrustTier** - Trust tier validation for all modules
3. **Imports** - Proper import restrictions
4. **SafeVerify** - Optional kernel-level verification (--safeverify flag)
-/

namespace TAIL.Checks

open Lean

/-! ## Run All Checks -/

/-- Run all verification checks using the olean-based reader.
    Returns a tuple of (check results, semantic warnings).
    Warnings don't affect pass/fail but should be shown in reports. -/
def runChecks (resolved : ResolvedConfig) : IO (List CheckResult × List String) := do
  -- Read all project modules
  let modules ← readProjectModules resolved

  if modules.isEmpty then
    return ([CheckResult.fail CheckCategory.structure "Module Loading"
      "No modules found"
      ["Ensure the project has been built with `lake build`",
       s!"Expected source directory: {resolved.sourcePath}"]], [])

  -- Run core checks
  let structureResult ← checkStructure resolved modules
  let trustTierResult ← checkTrustTier resolved modules
  let importsResult ← checkImports resolved modules

  -- Collect semantic risk warnings (these don't affect pass/fail)
  let semanticWarnings ← checkDefinitionsSemanticRisks resolved

  -- Optional SafeVerify check (only if enabled)
  let safeVerifyResults ← if resolved.runSafeVerify then
    let result ← runSafeVerify resolved
    pure [result]
  else
    pure []

  let checks := [
    structureResult,
    trustTierResult,
    importsResult
  ] ++ safeVerifyResults

  return (checks, semanticWarnings.toList)

end TAIL.Checks
