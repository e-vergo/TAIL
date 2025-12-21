/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean.Environment

/-!
# TAIL Shared Utilities

Common definitions used across multiple TAIL checks.
Consolidates duplicated code for consistency and maintainability.
-/

namespace TAIL

open Lean

/-! ## String Utilities -/

/-- Check if a string contains a substring. -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## Standard Library Imports -/

/-- Allowed import prefixes for standard libraries (Mathlib, Lean core, etc.).
    Used to distinguish project-local imports from external dependencies. -/
def standardLibraryPrefixes : List String :=
  ["Mathlib", "Init", "Std", "Lean", "Qq", "Aesop", "ProofWidgets", "Batteries"]

/-- Check if an import is from the standard library (Mathlib, Lean core, etc.). -/
def isStandardLibraryImport (moduleName : Name) : Bool :=
  let nameStr := moduleName.toString
  standardLibraryPrefixes.any (nameStr.startsWith ·)

/-! ## Module Introspection -/

/-- Get imports for a specific module from the environment.
    Returns `none` if the module is not found. -/
def getModuleImports (env : Environment) (moduleName : Name) : Option (Array Import) := do
  let idx ← env.getModuleIdx? moduleName
  let moduleData := env.header.moduleData[idx.toNat]?
  return moduleData.map (·.imports) |>.getD #[]

end TAIL
