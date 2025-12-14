/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean
import TAIL.Types

/-!
# TAIL Environment Utilities

Environment introspection utilities for verification.
All checks use proper Lean environment queries, not text parsing.
-/

namespace TAIL

open Lean Meta

/-! ## Module Membership Detection -/

/-- Get the module name for a declaration, if it exists in the environment -/
def getModuleName (env : Environment) (declName : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? declName
  env.header.moduleNames[idx.toNat]?

/-- Check if a declaration belongs to a specific module -/
def isInModule (env : Environment) (declName : Name) (moduleName : Name) : Bool :=
  match getModuleName env declName with
  | some name => name == moduleName
  | none => false

/-- Get all declarations defined in a specific module -/
def getModuleDeclarations (env : Environment) (moduleName : Name) : List Name := Id.run do
  let mut result : List Name := []
  for (name, _) in env.constants.toList do
    if isInModule env name moduleName then
      result := name :: result
  return result.reverse

/-! ## Internal Name Detection -/

/-- Check if a string contains a substring -/
private def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check if a name is an internal/auxiliary declaration -/
def isInternalName (name : Name) : Bool :=
  name.isInternal ||
  containsSubstr name.toString "._" ||
  containsSubstr name.toString ".match_" ||
  containsSubstr name.toString ".proof_"

/-! ## Type Checking Utilities -/

/-- Check if an expression is Prop (syntactically) -/
def isPropSyntactic (e : Expr) : Bool :=
  e.isSort && e.sortLevel! == Level.zero

/-- Check if an expression is definitionally equal to Prop -/
def isPropDefEq (e : Expr) : MetaM Bool := do
  isDefEq e (Expr.sort Level.zero)

/-- Get declaration kind as a string -/
def getDeclKind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-! ## Re-Import Test (Module Visibility Checking) -/

/-- Check if a module name belongs to the project (starts with project prefix) -/
def isProjectModule (moduleName : Name) (projectPrefix : String) : Bool :=
  moduleName.toString.startsWith projectPrefix

/-- Get all visible declarations that come from project modules.
    Checks module membership rather than name prefix, since declarations
    may be in the global namespace (e.g., StatementOfTheorem, mainTheorem). -/
def getVisibleProjectDeclarations (env : Environment) (projectPrefix : String) : List Name := Id.run do
  let mut visible : List Name := []

  for (name, _) in env.constants.toList do
    -- Skip internal names
    if isInternalName name then continue
    -- Skip names starting with _private (module-private declarations)
    if name.toString.startsWith "_private" then continue

    -- Check if this declaration comes from a project module
    match getModuleName env name with
    | some modName =>
      if isProjectModule modName projectPrefix then
        visible := name :: visible
    | none => continue

  return visible.reverse

/-- Filter to user-defined declarations (defs and theorems) -/
def filterUserDeclarations (env : Environment) (names : List Name) : List Name :=
  names.filter fun name =>
    match env.find? name with
    | some (.defnInfo _) | some (.thmInfo _) => true
    | _ => false

/-- Check if a module is a "core" module (MainTheorem or ProofOfMainTheorem) -/
def isCoreModule (moduleName : Name) (projectPrefix : String) : Bool :=
  let mainMod := s!"{projectPrefix}.MainTheorem".toName
  let proofMod := s!"{projectPrefix}.ProofOfMainTheorem".toName
  moduleName == mainMod || moduleName == proofMod

/-- The re-import test: verify only allowed declarations are exported from the proof module.
    When ProofOfMainTheorem is imported, only StatementOfTheorem and mainTheorem should be
    visible from project modules. Helper declarations must be private (using module system). -/
def checkModuleVisibility (env : Environment) (projectPrefix : String)
    (statementName theoremName : Name) : CheckResult := Id.run do
  -- Get all declarations from project modules in the loaded environment
  let projectDecls := getVisibleProjectDeclarations env projectPrefix

  -- Filter to user-defined declarations (defs and theorems)
  let userDecls := filterUserDeclarations env projectDecls

  -- The only allowed exports are:
  -- 1. StatementOfTheorem (def in MainTheorem.lean)
  -- 2. mainTheorem (theorem in ProofOfMainTheorem.lean)
  let allowed := [statementName, theoremName]

  -- Any project declaration that's not in the allowed list is a violation
  let violations := userDecls.filter fun d => !allowed.contains d

  if violations.isEmpty then
    CheckResult.pass "Module Visibility"
      s!"Only {statementName.toString.splitOn "." |>.getLast!} and {theoremName.toString.splitOn "." |>.getLast!} are exported from project modules"
  else
    let details := violations.map fun v =>
      let modName := match getModuleName env v with
        | some m => m.toString
        | none => "unknown"
      s!"Leaked: {v} (from {modName})"
    CheckResult.fail "Module Visibility"
      s!"{violations.length} internal declarations leaked from project modules"
      details

end TAIL
