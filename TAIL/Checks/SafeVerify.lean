/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# SafeVerify Integration

Optional kernel-level verification via SafeVerify subprocess.
Enabled with --safeverify flag.
-/

namespace TAIL.Checks

open Lean

/-- Construct the olean path for a module name.
    Olean files are at: projectRoot / ".lake/build/lib/lean" / (module path) ++ ".olean" -/
private def oleanPath (projectRoot : System.FilePath) (moduleName : Name) : System.FilePath :=
  let moduleRelPath := moduleName.toString.replace "." "/"
  projectRoot / ".lake" / "build" / "lib" / "lean" / (moduleRelPath ++ ".olean")

/-- Check if SafeVerify is available by running `lake exe safe_verify --help`. -/
private def checkSafeVerifyAvailable (projectRoot : System.FilePath) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "safe_verify", "--help"]
    cwd := some projectRoot
  }
  return result.exitCode == 0

/-- Run SafeVerify as subprocess for kernel-level verification.
    Returns CheckResult with pass/fail and detailed output. -/
def runSafeVerify (resolved : ResolvedConfig) : IO CheckResult := do
  let projectRoot := resolved.projectRoot
  let targetModule := resolved.mainTheoremModule
  let submissionModule := resolved.proofOfMainTheoremModule

  -- Construct olean paths
  let targetOlean := oleanPath projectRoot targetModule
  let submissionOlean := oleanPath projectRoot submissionModule

  -- Check target olean exists
  let targetExists ← targetOlean.pathExists
  if !targetExists then
    return CheckResult.fail CheckCategory.soundness "SafeVerify"
      s!"Target olean file not found: {targetOlean}"
      ["Ensure the project has been built with `lake build`",
       s!"Expected olean for module: {targetModule}"]

  -- Check submission olean exists
  let submissionExists ← submissionOlean.pathExists
  if !submissionExists then
    return CheckResult.fail CheckCategory.soundness "SafeVerify"
      s!"Submission olean file not found: {submissionOlean}"
      ["Ensure the project has been built with `lake build`",
       s!"Expected olean for module: {submissionModule}"]

  -- Check SafeVerify is available
  let safeVerifyAvailable ← checkSafeVerifyAvailable projectRoot
  if !safeVerifyAvailable then
    return CheckResult.fail CheckCategory.soundness "SafeVerify"
      "SafeVerify tool not available"
      ["SafeVerify must be added as a dependency in lakefile.toml",
       "Run `lake exe safe_verify --help` to verify installation"]

  -- Run SafeVerify: lake exe safe_verify <target.olean> <submission.olean>
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "safe_verify", targetOlean.toString, submissionOlean.toString]
    cwd := some projectRoot
  }

  -- Parse result based on exit code
  if result.exitCode == 0 then
    let message := if result.stdout.trim.isEmpty then
      "Kernel-level verification passed"
    else
      result.stdout.trim
    return CheckResult.pass CheckCategory.soundness "SafeVerify" message
  else
    let errorMsg := if result.stderr.trim.isEmpty then
      result.stdout.trim
    else
      result.stderr.trim
    let details := if errorMsg.isEmpty then
      ["SafeVerify exited with code: " ++ toString result.exitCode]
    else
      errorMsg.splitOn "\n" |>.filter (!·.trim.isEmpty)
    return CheckResult.fail CheckCategory.soundness "SafeVerify"
      "Kernel-level verification failed"
      details

end TAIL.Checks
