/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KM_Inspect.Types

/-!
# KM_Inspect Configuration

Auto-detect project configuration from lakefile.lean with hardcoded Kim Morrison Standard names.

No configuration file needed - all names are standardized:
- MainTheorem.lean, ProofOfMainTheorem.lean
- StatementOfTheorem, mainTheorem
-/

namespace KM_Inspect

open Lean

/-! ## Hardcoded Kim Morrison Standard Names -/

/-- Standard file name for the theorem statement -/
def kmMainTheoremFile : String := "MainTheorem.lean"

/-- Standard file name for the theorem proof -/
def kmProofOfMainTheoremFile : String := "ProofOfMainTheorem.lean"

/-- Standard name for the statement definition -/
def kmStatementName : String := "StatementOfTheorem"

/-- Standard name for the main theorem -/
def kmTheoremName : String := "mainTheorem"

/-! ## Resolved Configuration -/

/-- Resolved configuration with auto-detected project prefix -/
structure ResolvedConfig where
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
  deriving Inhabited, Repr

/-- Parse a dot-separated string into a hierarchical Name -/
private def parseDottedName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) Name.anonymous

/-- Fully qualified name for StatementOfTheorem.
    In Lean 4, top-level declarations go to root namespace, so it's just `StatementOfTheorem`. -/
def ResolvedConfig.statementName (_ : ResolvedConfig) : Name :=
  kmStatementName.toName

/-- Fully qualified name for mainTheorem.
    In Lean 4, top-level declarations go to root namespace, so it's just `mainTheorem`. -/
def ResolvedConfig.theoremName (_ : ResolvedConfig) : Name :=
  kmTheoremName.toName

/-- Module name for MainTheorem -/
def ResolvedConfig.mainTheoremModule (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.MainTheorem"

/-- Module name for ProofOfMainTheorem -/
def ResolvedConfig.proofOfMainTheoremModule (rc : ResolvedConfig) : Name :=
  parseDottedName s!"{rc.projectPrefix}.ProofOfMainTheorem"

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

/-- Resolve configuration with an explicit project prefix. -/
def resolveWithPrefix (projectRoot : System.FilePath) (projectPrefix : String) : IO (Except String ResolvedConfig) := do
  -- Source directory uses project prefix as name (standard convention)
  let sourcePath := projectRoot / projectPrefix

  -- Verify source directory exists
  let sourceExists ← sourcePath.pathExists
  if !sourceExists then
    return .error s!"Source directory not found: {sourcePath}"

  -- Resolve paths using hardcoded names
  let mainTheoremPath := sourcePath / kmMainTheoremFile
  let proofOfMainTheoremPath := sourcePath / kmProofOfMainTheoremFile

  -- Verify required files exist
  let mainExists ← mainTheoremPath.pathExists
  if !mainExists then
    return .error s!"{kmMainTheoremFile} not found: {mainTheoremPath}"

  let proofExists ← proofOfMainTheoremPath.pathExists
  if !proofExists then
    return .error s!"{kmProofOfMainTheoremFile} not found: {proofOfMainTheoremPath}"

  return .ok {
    projectPrefix
    projectRoot
    sourcePath
    mainTheoremPath
    proofOfMainTheoremPath
  }

/-- Resolve configuration from a directory path.
    Auto-detects project prefix from lakefile and uses hardcoded standard names. -/
def resolveFromDirectory (projectRoot : System.FilePath) : IO (Except String ResolvedConfig) := do
  -- Extract project prefix from lakefile
  match ← extractProjectPrefix projectRoot with
  | .error e => return .error e
  | .ok projectPrefix => resolveWithPrefix projectRoot projectPrefix

/-! ## Trust Level Detection -/

/-- Determine trust level for a file path.
    In the strict Kim Morrison standard, there are only two tiers. -/
def getTrustLevel (resolved : ResolvedConfig) (path : System.FilePath) : TrustLevel :=
  let pathStr := path.toString
  if pathStr == resolved.mainTheoremPath.toString then
    TrustLevel.MainTheorem
  else
    TrustLevel.ProofOfMainTheorem

end KM_Inspect
