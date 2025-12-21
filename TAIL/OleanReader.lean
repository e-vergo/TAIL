/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean
import TAIL.Types
import TAIL.Config

/-!
# TAIL Olean Reader

Fast olean-based module reading for TAIL verification.
Uses `Lean.readModuleData` to read olean files directly without importing dependencies.

This module provides efficient access to declaration information from compiled Lean modules,
enabling verification checks without full environment loading.
-/

namespace TAIL

open Lean

/-! ## Declaration Kind -/

/-- Kind of a Lean declaration, matching ConstantInfo variants -/
inductive DeclKind where
  | defn
  | thm
  | ax
  | opaq
  | quot
  | ind
  | ctor
  | recr
  deriving Inhabited, BEq, Repr

instance : ToString DeclKind where
  toString
    | .defn => "def"
    | .thm => "theorem"
    | .ax => "axiom"
    | .opaq => "opaque"
    | .quot => "quot"
    | .ind => "inductive"
    | .ctor => "constructor"
    | .recr => "recursor"

/-- Convert ConstantInfo to DeclKind -/
def DeclKind.fromConstantInfo : ConstantInfo → DeclKind
  | .defnInfo _ => .defn
  | .thmInfo _ => .thm
  | .axiomInfo _ => .ax
  | .opaqueInfo _ => .opaq
  | .quotInfo _ => .quot
  | .inductInfo _ => .ind
  | .ctorInfo _ => .ctor
  | .recInfo _ => .recr

/-- Check if a DeclKind is a definition -/
def DeclKind.isDef : DeclKind → Bool
  | .defn => true
  | _ => false

/-- Check if a DeclKind is a theorem -/
def DeclKind.isTheorem : DeclKind → Bool
  | .thm => true
  | _ => false

/-! ## Olean Declaration Info -/

/-- Information about a declaration extracted from olean -/
structure OleanDeclInfo where
  /-- Fully qualified name of the declaration -/
  name : Name
  /-- Kind of declaration (def, theorem, axiom, etc.) -/
  kind : DeclKind
  /-- Type of the declaration -/
  type : Expr
  /-- Direct dependencies (constants used in type and value) -/
  usedConstants : Array Name
  deriving Inhabited

instance : ToString OleanDeclInfo where
  toString info := s!"{info.kind} {info.name}"

/-- Extract OleanDeclInfo from a ConstantInfo -/
def OleanDeclInfo.fromConstantInfo (info : ConstantInfo) : OleanDeclInfo :=
  let usedConstants := info.getUsedConstantsAsSet.toArray
  { name := info.name
    kind := DeclKind.fromConstantInfo info
    type := info.type
    usedConstants := usedConstants }

/-! ## Olean Module Info -/

/-- Information about a module extracted from olean -/
structure OleanModuleInfo where
  /-- Module name (e.g., `Example.MainTheorem`) -/
  name : Name
  /-- Path to the olean file -/
  path : System.FilePath
  /-- Direct imports of the module -/
  imports : Array Import
  /-- All declarations in the module -/
  declarations : Array OleanDeclInfo
  deriving Inhabited

instance : ToString OleanModuleInfo where
  toString info := s!"Module {info.name}: {info.declarations.size} declarations, {info.imports.size} imports"

/-! ## Olean Path Resolution -/

/-- Find olean path for a module name given project root.
    Olean files are located at `.lake/build/lib/lean/{ModulePath}.olean`
    where ModulePath replaces `.` with `/` in the module name. -/
def findOleanPath (projectRoot : System.FilePath) (moduleName : Name) : System.FilePath :=
  let modulePath := moduleName.toString.replace "." "/"
  projectRoot / ".lake" / "build" / "lib" / "lean" / (modulePath ++ ".olean")

/-! ## Olean Reading -/

/-- Read module info directly from an olean file.

    Uses `Lean.readModuleData` to load the olean file and extracts declaration
    information. The compacted region is held in memory while extracting data,
    then freed after the extraction is complete.

    Throws an IO error if the file cannot be read or is malformed. -/
def readOleanModule (oleanPath : System.FilePath) (moduleName : Name) : IO OleanModuleInfo := do
  -- Check if file exists first for better error messages
  unless (← oleanPath.pathExists) do
    throw <| IO.userError s!"Olean file not found: {oleanPath}"

  -- Read the module data (returns ModuleData and CompactedRegion)
  let (moduleData, _region) ← Lean.readModuleData oleanPath

  -- Extract declaration info while the region is alive
  let declarations := moduleData.constants.map OleanDeclInfo.fromConstantInfo

  -- Copy the import array (imports are small, safe to copy)
  let imports := moduleData.imports

  -- Note: We cannot safely free the region here because the Expr values
  -- in declarations still reference memory in the compacted region.
  -- The caller must ensure the OleanModuleInfo does not outlive its use,
  -- or the Expr values should be serialized/processed before the region is freed.
  --
  -- In practice, for TAIL verification, we only need the usedConstants (Array Name)
  -- and declaration metadata, which are copied out and safe.
  --
  -- SAFETY: We keep the region alive by not calling region.free.
  -- This is intentional - the region will be freed when the process exits.
  -- For long-running processes, consider using a different approach.

  return {
    name := moduleName
    path := oleanPath
    imports := imports
    declarations := declarations
  }

/-- Read module info with automatic path resolution.
    Combines `findOleanPath` and `readOleanModule`. -/
def readOleanModuleFromProject (projectRoot : System.FilePath) (moduleName : Name) : IO OleanModuleInfo := do
  let oleanPath := findOleanPath projectRoot moduleName
  readOleanModule oleanPath moduleName

/-! ## Project Module Discovery -/

/-- Discover all Lean source files in a directory recursively.
    Returns paths relative to the given directory.
    Excludes lakefile.lean which is a Lake config file, not a module. -/
private partial def discoverLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  if !(← dir.pathExists) then return files
  for entry in (← dir.readDir) do
    let path := entry.path
    if (← path.isDir) then
      let subFiles ← discoverLeanFiles path
      files := files ++ subFiles
    else if path.extension == some "lean" && entry.fileName != "lakefile.lean" then
      files := files.push path
  return files

/-- Convert a file path to a module name.
    E.g., `./Example/MainTheorem.lean` with prefix `Example` -> `Example.MainTheorem` -/
private def filePathToModuleName (projectRoot : System.FilePath) (projectPrefix : String) (filePath : System.FilePath) : Option Name := do
  -- Get relative path from project root
  let fileStr := filePath.toString
  let rootStr := projectRoot.toString
  guard (fileStr.startsWith rootStr)
  let relPath := fileStr.drop (rootStr.length + 1)  -- +1 for separator
  -- Remove .lean extension and convert / to .
  let withoutExt := relPath.dropEnd 5  -- ".lean".length
  let moduleName := withoutExt.replace "/" "."
  -- Only include if it starts with project prefix
  guard (moduleName.startsWith projectPrefix)
  return moduleName.toName

/-- Get all module names from a ResolvedConfig.
    Discovers all .lean files in the project source directory. -/
def discoverProjectModules (resolved : ResolvedConfig) : IO (Array Name) := do
  let leanFiles ← discoverLeanFiles resolved.sourcePath
  let moduleNames := leanFiles.filterMap (filePathToModuleName resolved.projectRoot resolved.projectPrefix ·)
  return moduleNames

/-- Read all project modules from a ResolvedConfig.

    Discovers all modules in the project and reads their olean files.
    Modules whose olean files are missing or unreadable are skipped with a warning. -/
def readProjectModules (resolved : ResolvedConfig) : IO (Array OleanModuleInfo) := do
  let moduleNames ← discoverProjectModules resolved
  let mut modules : Array OleanModuleInfo := #[]

  for moduleName in moduleNames do
    let oleanPath := findOleanPath resolved.projectRoot moduleName
    if ← oleanPath.pathExists then
      try
        let moduleInfo ← readOleanModule oleanPath moduleName
        modules := modules.push moduleInfo
      catch e =>
        -- Log warning but continue with other modules
        IO.eprintln s!"Warning: Failed to read olean for {moduleName}: {e}"
    else
      IO.eprintln s!"Warning: Olean not found for {moduleName}, run `lake build` first"

  return modules

/-! ## Utility Functions -/

/-- Check if a string contains a substring -/
private def strContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Check if a declaration uses sorry.
    Checks if `sorryAx` is in the direct dependencies. -/
def OleanDeclInfo.usesSorry (decl : OleanDeclInfo) : Bool :=
  decl.usedConstants.contains ``sorryAx

/-- Alias for backwards compatibility -/
def usesSorry (decl : OleanDeclInfo) : Bool := decl.usesSorry

/-- Check if a name is from the project (not Mathlib/Init/etc).
    Uses the project prefix to determine project membership. -/
def isProjectDecl (name : Name) (projectPrefix : String) : Bool :=
  let nameStr := name.toString
  nameStr.startsWith projectPrefix || nameStr.startsWith s!"_private.0.{projectPrefix}"

/-- Filter declarations to only those from the project -/
def OleanModuleInfo.projectDeclarations (info : OleanModuleInfo) (projectPrefix : String) : Array OleanDeclInfo :=
  info.declarations.filter (isProjectDecl ·.name projectPrefix)

/-- Check if a declaration is a user-defined declaration (def or theorem) -/
def OleanDeclInfo.isUserDefined (decl : OleanDeclInfo) : Bool :=
  decl.kind.isDef || decl.kind.isTheorem

/-- Get all user-defined declarations from a module -/
def OleanModuleInfo.userDeclarations (info : OleanModuleInfo) : Array OleanDeclInfo :=
  info.declarations.filter (·.isUserDefined)

/-- Check if a declaration is internal/auxiliary -/
def OleanDeclInfo.isInternal (decl : OleanDeclInfo) : Bool :=
  decl.name.isInternal ||
  strContains decl.name.toString "._" ||
  strContains decl.name.toString ".match_" ||
  strContains decl.name.toString ".proof_"

/-- Get non-internal declarations from a module -/
def OleanModuleInfo.publicDeclarations (info : OleanModuleInfo) : Array OleanDeclInfo :=
  info.declarations.filter (!·.isInternal)

/-! ## Dependency Analysis -/

/-- Get all constants that a declaration depends on, filtered to project declarations -/
def OleanDeclInfo.projectDependencies (decl : OleanDeclInfo) (projectPrefix : String) : Array Name :=
  decl.usedConstants.filter (isProjectDecl · projectPrefix)

/-- Get all declarations in a module that use sorry -/
def OleanModuleInfo.sorryDeclarations (info : OleanModuleInfo) : Array OleanDeclInfo :=
  info.declarations.filter (·.usesSorry)

/-- Check if any declaration in the module uses sorry -/
def OleanModuleInfo.hasSorry (info : OleanModuleInfo) : Bool :=
  info.declarations.any (·.usesSorry)

end TAIL
