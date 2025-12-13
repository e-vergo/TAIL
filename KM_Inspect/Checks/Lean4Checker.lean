/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KM_Inspect.Types
import KM_Inspect.Config

/-!
# Lean4Checker Integration

Run lean4checker to verify kernel acceptance of all declarations.

lean4checker replays the environment to detect "environment hacking" -
using metaprogramming to build an inconsistent environment.

See: https://github.com/leanprover/lean4checker
-/

namespace KM_Inspect.Checks

/-- Run lean4checker to verify kernel acceptance of ProofOfMainTheorem module.

This invokes `lake exe lean4checker <module>` as a subprocess.
lean4checker replays all declarations through the kernel to verify they are
accepted without any metaprogramming tricks. -/
def checkLean4Checker (resolved : ResolvedConfig) : IO CheckResult := do
  let moduleName := s!"{resolved.projectPrefix}.ProofOfMainTheorem"

  -- Run lean4checker as subprocess
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "lean4checker", moduleName]
    cwd := some resolved.projectRoot
  }

  if output.exitCode == 0 then
    return CheckResult.pass "Lean4Checker"
      s!"Kernel verification passed for {moduleName}"
  else
    -- Extract meaningful error message
    let errorMsg := if output.stderr.isEmpty then output.stdout else output.stderr
    let details := errorMsg.splitOn "\n"
      |>.filter (fun s => !s.isEmpty)
      |>.take 10  -- Limit to first 10 lines
    return CheckResult.fail "Lean4Checker"
      s!"Kernel verification failed for {moduleName}"
      details

end KM_Inspect.Checks
