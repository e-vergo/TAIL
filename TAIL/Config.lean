/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types

/-!
# TAIL Configuration

Auto-detect project configuration from lakefile.lean with hardcoded TAIL Standard names.

No configuration file needed - all names are standardized:
- MainTheorem.lean, ProofOfMainTheorem.lean
- Definitions/, Proofs/
- ProjectName.StatementOfTheorem, ProjectName.mainTheorem
-/

namespace TAIL

open Lean

/-! ## Hardcoded TAIL Standard Names -/

/-- Standard file name for the theorem statement -/
def mainTheoremFile : String := "MainTheorem.lean"

/-- Standard file name for the theorem proof -/
def proofOfMainTheoremFile : String := "ProofOfMainTheorem.lean"

/-- Standard folder name for definitions (default mode only) -/
def definitionsFolder : String := "Definitions"

/-- Standard folder name for proof helpers -/
def proofsFolder : String := "Proofs"

/-- Standard name for the statement definition (without namespace) -/
def statementBaseName : String := "StatementOfTheorem"

/-- Standard name for the main theorem (without namespace) -/
def theoremBaseName : String := "mainTheorem"

/-! ## Resolved Configuration -/

/-- Resolved configuration with auto-detected project prefix -/
structure ResolvedConfig where
  /-- Verification mode (strict or default) -/
  mode : VerificationMode
  /-- Auto-detected project prefix from lakefile -/
  projectPrefix : String
  /-- Absolute project root path -/
  projectRoot : System.FilePath
  /-- Absolute path to source directory ({projectPrefix}/) -/
  sourcePath : System.FilePath
  /-- Absolute path to MainTheorem.lean -/
  mainTheoremPath : System.FilePath
  /-- Absolute path to ProofOfMainTheorem.lean -/
  proofOfMainTheoremPath : System.FilePath
  /-- Absolute path to Definitions/ folder (default mode only) -/
  definitionsPath : Option System.FilePath
  /-- Absolute path to Proofs/ folder (optional) -/
  proofsPath : Option System.FilePath
  deriving Inhabited, Repr

/-- Parse a dot-separated string into a hierarchical Name -/
private def parseDottedName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) Name.anonymous

/-- Fully qualified name for StatementOfTheorem.
    Per the TAIL standard, uses ProjectName.StatementOfTheorem to prevent collisions. -/
def ResolvedConfig.statementName' (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.{statementBaseName}"

/-- Fully qualified name for mainTheorem.
    Per the TAIL standard, uses ProjectName.mainTheorem to prevent collisions. -/
def ResolvedConfig.theoremName' (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.{theoremBaseName}"

/-- Module name for MainTheorem -/
def ResolvedConfig.mainTheoremModule (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.MainTheorem"

/-- Module name for ProofOfMainTheorem -/
def ResolvedConfig.proofOfMainTheoremModule (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.ProofOfMainTheorem"

/-- Module name prefix for Definitions/ -/
def ResolvedConfig.definitionsModulePrefix (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.{definitionsFolder}"

/-- Module name prefix for Proofs/ -/
def ResolvedConfig.proofsModulePrefix (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.{proofsFolder}"

/-- Check if a module is in the Definitions/ folder -/
def ResolvedConfig.isDefinitionsModule (rc : ResolvedConfig) (moduleName : Name) : Bool :=
  moduleName.toString.startsWith s!"{rc.projectPrefix}.{definitionsFolder}"

/-- Check if a module is in the Proofs/ folder -/
def ResolvedConfig.isProofsModule (rc : ResolvedConfig) (moduleName : Name) : Bool :=
  moduleName.toString.startsWith s!"{rc.projectPrefix}.{proofsFolder}"

/-! ## Lakefile Parsing -/

/-- Extract project prefix from lakefile.lean by finding "package <Name> where" -/
def extractProjectPrefix (projectRoot : System.FilePath) : IO (Except String String) := do
  let lakefilePath := projectRoot / "lakefile.lean"
  let lakefileExists ← lakefilePath.pathExists
  if !lakefileExists then
    -- Try lakefile.toml as fallback
    let tomlPath := projectRoot / "lakefile.toml"
    let tomlExists ← tomlPath.pathExists
    if !tomlExists then
      return .error "No lakefile.lean or lakefile.toml found in project root"
    -- Parse TOML format: name = "ProjectName"
    let content ← IO.FS.readFile tomlPath
    for line in content.splitOn "\n" do
      let trimmed := line.trimAscii
      if trimmed.startsWith "name = " then
        let rest := trimmed.drop 7  -- "name = ".length
        let name := rest.trimAscii.dropWhile (· == '"') |> (·.dropEndWhile (· == '"'))
        if name.isEmpty then continue
        return .ok name.toString
    return .error "Could not find 'name = \"...\"' in lakefile.toml"

  -- Parse lakefile.lean: package <Name> where
  let content ← IO.FS.readFile lakefilePath
  for line in content.splitOn "\n" do
    let trimmed := line.trimAscii
    if trimmed.startsWith "package " then
      let rest := trimmed.drop 8  -- "package ".length
      let name := rest.takeWhile (fun c => c != ' ' && c != '\n')
      if name.isEmpty then continue
      return .ok name.toString
  return .error "Could not find 'package <Name> where' in lakefile.lean"

/-! ## Resolution -/

/-- Resolve configuration with an explicit project prefix and mode. -/
def resolveWithPrefix (projectRoot : System.FilePath) (projectPrefix : String) (mode : VerificationMode) : IO (Except String ResolvedConfig) := do
  -- Source directory uses project prefix as name (standard convention)
  let sourcePath := projectRoot / projectPrefix

  -- Verify source directory exists
  let sourceExists ← sourcePath.pathExists
  if !sourceExists then
    return .error s!"Source directory not found: {sourcePath}"

  -- Resolve paths using hardcoded names
  let mainTheoremPath := sourcePath / mainTheoremFile
  let proofOfMainTheoremPath := sourcePath / proofOfMainTheoremFile

  -- Verify required files exist
  let mainExists ← mainTheoremPath.pathExists
  if !mainExists then
    return .error s!"{mainTheoremFile} not found: {mainTheoremPath}"

  let proofExists ← proofOfMainTheoremPath.pathExists
  if !proofExists then
    return .error s!"{proofOfMainTheoremFile} not found: {proofOfMainTheoremPath}"

  -- Check for optional Definitions/ folder
  let definitionsPath := sourcePath / definitionsFolder
  let definitionsExists ← definitionsPath.pathExists
  let definitionsOpt := if definitionsExists then some definitionsPath else none

  -- In strict mode, Definitions/ folder is not allowed
  if mode == .strict && definitionsExists then
    return .error s!"Definitions/ folder found but strict mode is enabled. Use default mode or remove {definitionsPath}"

  -- Check for optional Proofs/ folder
  let proofsPath := sourcePath / proofsFolder
  let proofsExists ← proofsPath.pathExists
  let proofsOpt := if proofsExists then some proofsPath else none

  return .ok {
    mode
    projectPrefix
    projectRoot
    sourcePath
    mainTheoremPath
    proofOfMainTheoremPath
    definitionsPath := definitionsOpt
    proofsPath := proofsOpt
  }

/-- Resolve configuration from a directory path.
    Auto-detects project prefix from lakefile and uses hardcoded standard names. -/
def resolveFromDirectory (projectRoot : System.FilePath) (mode : VerificationMode := .default) : IO (Except String ResolvedConfig) := do
  -- Extract project prefix from lakefile
  match ← extractProjectPrefix projectRoot with
  | .error e => return .error e
  | .ok projectPrefix => resolveWithPrefix projectRoot projectPrefix mode

/-! ## Trust Level Detection -/

/-- Determine trust level for a file path. -/
def getTrustLevel (resolved : ResolvedConfig) (path : System.FilePath) : TrustLevel :=
  let pathStr := path.toString
  -- Check exact matches first
  if pathStr == resolved.mainTheoremPath.toString then
    TrustLevel.MainTheorem
  else if pathStr == resolved.proofOfMainTheoremPath.toString then
    TrustLevel.ProofOfMainTheorem
  -- Check directory membership
  else if resolved.definitionsPath.any (pathStr.startsWith ·.toString) then
    TrustLevel.Definitions
  else
    -- All other project files (including Proofs/) are machine-verified
    TrustLevel.Proofs

/-- Determine trust level for a module name. -/
def getTrustLevelForModule (resolved : ResolvedConfig) (moduleName : Name) : TrustLevel :=
  let modStr := moduleName.toString
  if moduleName == resolved.mainTheoremModule then
    TrustLevel.MainTheorem
  else if moduleName == resolved.proofOfMainTheoremModule then
    TrustLevel.ProofOfMainTheorem
  else if resolved.isDefinitionsModule moduleName then
    TrustLevel.Definitions
  else if resolved.isProofsModule moduleName then
    TrustLevel.Proofs
  else if modStr.startsWith resolved.projectPrefix then
    -- Other project modules default to Proofs (machine verified)
    TrustLevel.Proofs
  else
    -- Non-project modules (Mathlib, etc.) - shouldn't happen in normal use
    TrustLevel.Proofs

end TAIL
