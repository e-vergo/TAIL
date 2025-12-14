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

/-- Get all project declarations visible in the environment.
    These are declarations from modules starting with the project prefix. -/
def getVisibleProjectDeclarations (env : Environment) (projectPrefix : String) : List Name := Id.run do
  let mut visible : List Name := []
  let prefix_ := projectPrefix ++ "."

  for (name, _) in env.constants.toList do
    let nameStr := name.toString
    -- Only look at project declarations
    if !nameStr.startsWith prefix_ then continue
    -- Skip internal names
    if isInternalName name then continue
    visible := name :: visible

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
    visible from the core modules. Declarations from privately-imported helper modules
    are allowed (they won't be re-exported). -/
def checkModuleVisibility (env : Environment) (projectPrefix : String)
    (statementName theoremName : Name) : CheckResult := Id.run do
  -- Get all project declarations in the loaded environment
  let projectDecls := getVisibleProjectDeclarations env projectPrefix

  -- Filter to user-defined declarations (defs and theorems)
  let userDecls := filterUserDeclarations env projectDecls

  -- The only allowed exports FROM CORE MODULES are:
  -- 1. StatementOfTheorem (def in MainTheorem.lean)
  -- 2. mainTheorem (theorem in ProofOfMainTheorem.lean)
  let allowed := [statementName, theoremName]

  -- Only flag violations from core modules (MainTheorem, ProofOfMainTheorem)
  -- Declarations from privately-imported helper modules are OK
  let violations := userDecls.filter fun d =>
    if allowed.contains d then false
    else
      match getModuleName env d with
      | some modName => isCoreModule modName projectPrefix
      | none => false

  if violations.isEmpty then
    CheckResult.pass "Module Visibility"
      s!"Only {statementName.toString.splitOn "." |>.getLast!} and {theoremName.toString.splitOn "." |>.getLast!} are exported from core modules"
  else
    let details := violations.map fun v =>
      let modName := match getModuleName env v with
        | some m => m.toString
        | none => "unknown"
      s!"Leaked: {v} (from {modName})"
    CheckResult.fail "Module Visibility"
      s!"{violations.length} internal declarations leaked from core modules"
      details

end TAIL
