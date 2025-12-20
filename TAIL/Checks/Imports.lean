/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# Import Discipline Check (Environment-Based)

Verify imports follow the strict TAIL Standard using environment introspection.

Instead of parsing text for `public import`/`module` keywords, we verify the
**actual effect** by checking what declarations are visible in the loaded environment.

**MainTheorem.lean**:
- Can ONLY import Mathlib, Init, Lean, Batteries (verified via env.header.imports)

**ProofOfMainTheorem.lean**:
- Only StatementOfTheorem and mainTheorem should be exported
- All internal helpers must be private (verified via re-import test)
-/

namespace TAIL.Checks

open Lean

/-- Check imports using environment introspection.
    This performs the "re-import test" - verifying what's actually visible
    rather than checking for syntactic markers. -/
def checkImports (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv

  -- Verify module visibility using the re-import test
  let visibilityResult := checkModuleVisibility env
    resolved.projectPrefix
    resolved.statementName'
    resolved.theoremName'
    resolved.mode

  return visibilityResult

end TAIL.Checks
