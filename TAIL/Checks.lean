/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers
import TAIL.Checks.Soundness
import TAIL.Checks.FileStructure
import TAIL.Checks.Imports
import TAIL.Checks.ContentRules

/-!
# TAIL Checks

Verification checks using OleanReader instead of full environment loading.
This module re-exports all check functions from submodules and provides
the main `runChecks` orchestrator.

## Checks

1. **Structure** - Required declarations exist
2. **Soundness** - No sorry, native_decide, trivial True, partial, unsafe
3. **Axioms in Source** - No axiom declarations in source files
4. **Opaques in Source** - No opaque declarations in source files
5. **Unsafe Attributes** - No implemented_by or extern in source files
6. **ProofOfMainTheorem Isolation** - ProofOfMainTheorem has exactly one theorem
7. **MainTheorem Isolation** - MainTheorem has only allowed declarations
8. **Import Discipline** - Proper import restrictions
9. **Proofs Content** - Proofs/ contains only lemmas and Prop-valued defs
10. **Definitions Content** - Definitions/ contains only defs/structures
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

  -- Run all checks
  let structureResult ← checkStructure resolved modules
  let soundnessResult ← checkSoundness resolved modules
  let axiomsInSourceResult ← checkAxiomsInSource resolved
  let opaquesInSourceResult ← checkOpaquesInSource resolved
  let unsafeAttrsResult ← checkUnsafeAttributesInSource resolved
  let proofOfMainTheoremIsolationResult ← checkProofOfMainTheoremIsolation resolved modules
  let mainTheoremIsolationResult ← checkMainTheoremIsolation resolved modules
  let importsResult ← checkImports resolved modules
  let proofsContentResult ← checkProofsContent resolved modules
  let defsContentResult ← checkDefinitionsContent resolved modules

  -- Collect semantic risk warnings (these don't affect pass/fail)
  let semanticWarnings ← checkDefinitionsSemanticRisks resolved

  let checks := [
    structureResult,
    soundnessResult,
    axiomsInSourceResult,
    opaquesInSourceResult,
    unsafeAttrsResult,
    proofOfMainTheoremIsolationResult,
    mainTheoremIsolationResult,
    importsResult,
    proofsContentResult,
    defsContentResult
  ]

  return (checks, semanticWarnings.toList)

end TAIL.Checks
