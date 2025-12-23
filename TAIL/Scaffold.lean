/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

/-!
# TAIL Scaffold

Generate a new TAIL Standard project structure.

## Usage

```bash
lake exe tailscaffold <ProjectName>           # Default mode (with Definitions/)
lake exe tailscaffold --strict <ProjectName>  # Strict mode (Mathlib only)
```

## Default Mode Structure
```
ProjectName/
├── ProjectName/
│   ├── MainTheorem.lean
│   ├── ProofOfMainTheorem.lean
│   ├── Definitions/
│   │   └── Types.lean
│   └── Proofs/
│       └── Support.lean
├── lakefile.lean
└── lean-toolchain
```

## Strict Mode Structure
```
ProjectName/
├── ProjectName/
│   ├── MainTheorem.lean
│   ├── ProofOfMainTheorem.lean
│   └── Proofs/
│       └── Support.lean
├── lakefile.lean
└── lean-toolchain
```
-/

namespace TAIL.Scaffold

/-- Create a directory if it doesn't exist -/
def ensureDir (path : System.FilePath) : IO Unit := do
  let dirExists ← path.pathExists
  if !dirExists then
    IO.FS.createDirAll path

/-- Write a file with content -/
def writeFile (path : System.FilePath) (content : String) : IO Unit := do
  IO.FS.writeFile path content

/-- Generate MainTheorem.lean content for strict mode (Mathlib only) -/
def mainTheoremContentStrict (projectName : String) : String :=
s!"module

public import Mathlib.Tactic

namespace {projectName}

@[expose] public section

/-- The statement of the main theorem to be proven.

TODO: Replace this with your actual theorem statement.
In strict mode, all definitions must already exist in Mathlib.
-/
def StatementOfTheorem : Prop :=
  True  -- placeholder

end

end {projectName}
"

/-- Generate MainTheorem.lean content for default mode (Mathlib + Definitions/) -/
def mainTheoremContentDefault (projectName : String) : String :=
s!"module

public import Mathlib.Tactic
public import {projectName}.Definitions.Types

namespace {projectName}

@[expose] public section

/-- The statement of the main theorem to be proven.

TODO: Replace this with your actual theorem statement.
You can use definitions from Mathlib and from Definitions/.
-/
def StatementOfTheorem : Prop :=
  True  -- placeholder

end

end {projectName}
"

/-- Generate ProofOfMainTheorem.lean content -/
def proofOfMainTheoremContent (projectName : String) : String :=
s!"module

public import Mathlib.Tactic
public import {projectName}.MainTheorem
import {projectName}.Proofs.Support  -- Private (not re-exported)

namespace {projectName}

@[expose] public section

theorem mainTheorem : StatementOfTheorem := by
  trivial  -- TODO: Replace with your actual proof

end

end {projectName}
"

/-- Generate Proofs/Support.lean content -/
def proofsSupportContent (projectName : String) : String :=
s!"module

public import Mathlib.Tactic

namespace {projectName}.Proofs

public section

-- Add your supporting lemmas here

end

end {projectName}.Proofs
"

/-- Generate Definitions/Types.lean content (for default mode) -/
def definitionsTypesContent (projectName : String) : String :=
s!"module

public import Mathlib.Tactic

namespace {projectName}

@[expose] public section

-- Add your supporting types and definitions here
-- These will be available in MainTheorem.lean

end

end {projectName}
"

/-- Generate lakefile.lean content -/
def lakefileContent (projectName : String) : String :=
s!"import Lake
open Lake DSL

package {projectName} where
  version := v!\"0.1.0\"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
    -- Note: experimental.module is no longer required as of Lean 4.27+
  ]

require mathlib from git
  \"https://github.com/leanprover-community/mathlib4.git\"

require lean4checker from git
  \"https://github.com/leanprover/lean4checker\"

@[default_target]
lean_lib {projectName} where
  -- Library sources
"

/-- Generate lean-toolchain content -/
def toolchainContent : String :=
  "leanprover/lean4:v4.27.0-rc1"

/-- Generate the project structure -/
def scaffold (projectPath : String) (strictMode : Bool) : IO Unit := do
  let projectDir : System.FilePath := projectPath
  -- Extract just the directory name for the Lean module name
  let projectName := projectDir.fileName.getD projectPath
  let sourceDir := projectDir / projectName
  let proofsDir := sourceDir / "Proofs"
  let definitionsDir := sourceDir / "Definitions"

  -- Check if project already exists
  let projectExists ← projectDir.pathExists
  if projectExists then
    throw (IO.userError s!"Directory '{projectName}' already exists")

  let modeLabel := if strictMode then "strict" else "default"
  IO.println s!"Creating TAIL Standard project ({modeLabel} mode): {projectName}"
  IO.println ""

  -- Create directories
  IO.println "Creating directories..."
  ensureDir projectDir
  ensureDir sourceDir
  ensureDir proofsDir
  if !strictMode then
    ensureDir definitionsDir

  -- Write files
  IO.println "Writing files..."

  -- Main project files
  let mainTheoremContent := if strictMode
    then mainTheoremContentStrict projectName
    else mainTheoremContentDefault projectName
  writeFile (sourceDir / "MainTheorem.lean") mainTheoremContent
  IO.println s!"  {projectName}/{projectName}/MainTheorem.lean"

  writeFile (sourceDir / "ProofOfMainTheorem.lean") (proofOfMainTheoremContent projectName)
  IO.println s!"  {projectName}/{projectName}/ProofOfMainTheorem.lean"

  -- Proofs
  writeFile (proofsDir / "Support.lean") (proofsSupportContent projectName)
  IO.println s!"  {projectName}/{projectName}/Proofs/Support.lean"

  -- Definitions (default mode only)
  if !strictMode then
    writeFile (definitionsDir / "Types.lean") (definitionsTypesContent projectName)
    IO.println s!"  {projectName}/{projectName}/Definitions/Types.lean"

  -- Config files
  writeFile (projectDir / "lakefile.lean") (lakefileContent projectName)
  IO.println s!"  {projectName}/lakefile.lean"

  writeFile (projectDir / "lean-toolchain") toolchainContent
  IO.println s!"  {projectName}/lean-toolchain"

  IO.println ""
  IO.println "Project created successfully!"
  IO.println ""
  IO.println "Next steps:"
  IO.println s!"  1. cd {projectName}"
  IO.println "  2. lake update"
  IO.println "  3. lake exe cache get"
  if strictMode then
    IO.println "  4. Edit MainTheorem.lean to define your theorem statement"
    IO.println "  5. Add supporting lemmas in Proofs/"
    IO.println "  6. Complete the proof in ProofOfMainTheorem.lean"
    IO.println "  7. Run 'lake exe tailverify --strict' to verify compliance"
  else
    IO.println "  4. Add supporting types in Definitions/Types.lean"
    IO.println "  5. Edit MainTheorem.lean to define your theorem statement"
    IO.println "  6. Add supporting lemmas in Proofs/"
    IO.println "  7. Complete the proof in ProofOfMainTheorem.lean"
    IO.println "  8. Run 'lake exe tailverify' to verify compliance"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  -- Parse arguments
  let mut projectName : Option String := none
  let mut strictMode := false
  let mut showHelp := false

  for arg in args do
    if arg == "--strict" then
      strictMode := true
    else if arg == "--help" || arg == "-h" then
      showHelp := true
    else if !arg.startsWith "-" then
      projectName := some arg

  if showHelp then
    IO.println "Usage: lake exe tailscaffold [--strict] <ProjectName>"
    IO.println ""
    IO.println "Creates a new TAIL Standard project structure."
    IO.println ""
    IO.println "Options:"
    IO.println "  --strict    Create strict mode project (no Definitions/ folder)"
    IO.println "              Default mode includes Definitions/ for supporting types"
    IO.println ""
    IO.println "Examples:"
    IO.println "  lake exe tailscaffold MyTheorem           # Default mode"
    IO.println "  lake exe tailscaffold --strict MyTheorem  # Strict mode"
    return 0

  match projectName with
  | some name =>
    try
      scaffold name strictMode
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
  | none =>
    IO.eprintln "Usage: lake exe tailscaffold [--strict] <ProjectName>"
    IO.eprintln ""
    IO.eprintln "Run 'lake exe tailscaffold --help' for more information."
    return 1

end TAIL.Scaffold

/-- Entry point when run with lake exe -/
def main (args : List String) : IO UInt32 :=
  TAIL.Scaffold.main args
