/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

/-!
# TAIL Scaffold

Generate a new Kim Morrison Standard project structure.

## Usage

```bash
lake exe tailscaffold <ProjectName>
```

Creates:
- ProjectName/
  - ProjectName/
    - MainTheorem.lean (imports only Mathlib)
    - ProofOfMainTheorem.lean (uses module system)
    - Proofs/
      - Support.lean
  - lakefile.lean
  - lean-toolchain
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

/-- Generate MainTheorem.lean content (imports only Mathlib per Kim Morrison Standard) -/
def mainTheoremContent : String :=
"/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Main Theorem Statement

This file contains the statement of the main theorem to be proven.
Per the Kim Morrison Standard, this file:
- Imports ONLY from Mathlib (no project imports)
- Contains only definitions, no proofs
- Must be fully understood by a human reviewer
-/

/-- The statement of the main theorem to be proven.

TODO: Replace this with your actual theorem statement.
All definitions needed must either:
1. Already exist in Mathlib
2. Be defined in this file
-/
def StatementOfTheorem : Prop :=
  -- Replace with your theorem statement
  True  -- placeholder
"

/-- Generate ProofOfMainTheorem.lean content (uses module system) -/
def proofOfMainTheoremContent (projectName : String) : String :=
s!"/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module  -- Enable module system for private imports

public import Mathlib.Tactic       -- Re-exported to importers
import {projectName}.MainTheorem   -- Private (not re-exported)
import {projectName}.Proofs.Support -- Private (not re-exported)

/-!
# Proof of Main Theorem

This file contains exactly one theorem: the proof of the main theorem.
Per the Kim Morrison Standard:
- Uses `module` keyword to enable private imports
- All project imports are private (not re-exported)
- Only Mathlib imports are public
- Contains exactly one theorem in a public section
-/

public section

theorem mainTheorem : StatementOfTheorem := by
  -- TODO: Replace with your actual proof
  trivial
"

/-- Generate Proofs/Support.lean content -/
def proofsSupportContent (projectName : String) : String :=
s!"/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import {projectName}.MainTheorem
import Mathlib.Tactic

/-!
# Supporting Lemmas

This file contains supporting lemmas for the main theorem.
Files in the Proofs/ directory are machine-verified and don't require human review.
-/

namespace {projectName}.Proofs

-- Add your supporting lemmas here

end {projectName}.Proofs
"

/-- Generate lakefile.lean content -/
def lakefileContent (projectName : String) : String :=
s!"import Lake
open Lake DSL

package {projectName} where
  version := v!\"0.1.0\"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`experimental.module, true⟩  -- Required for Kim Morrison Standard
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
  "leanprover/lean4:v4.26.0"

/-- Generate the project structure -/
def scaffold (projectName : String) : IO Unit := do
  let projectDir : System.FilePath := projectName
  let sourceDir := projectDir / projectName
  let proofsDir := sourceDir / "Proofs"

  -- Check if project already exists
  let projectExists ← projectDir.pathExists
  if projectExists then
    throw (IO.userError s!"Directory '{projectName}' already exists")

  IO.println s!"Creating Kim Morrison Standard project: {projectName}"
  IO.println ""

  -- Create directories
  IO.println "Creating directories..."
  ensureDir projectDir
  ensureDir sourceDir
  ensureDir proofsDir

  -- Write files
  IO.println "Writing files..."

  -- Main project files
  writeFile (sourceDir / "MainTheorem.lean") mainTheoremContent
  IO.println s!"  {projectName}/{projectName}/MainTheorem.lean"

  writeFile (sourceDir / "ProofOfMainTheorem.lean") (proofOfMainTheoremContent projectName)
  IO.println s!"  {projectName}/{projectName}/ProofOfMainTheorem.lean"

  -- Proofs
  writeFile (proofsDir / "Support.lean") (proofsSupportContent projectName)
  IO.println s!"  {projectName}/{projectName}/Proofs/Support.lean"

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
  IO.println "  4. Edit MainTheorem.lean to define your theorem statement"
  IO.println "     (Remember: only Mathlib imports allowed!)"
  IO.println "  5. Add supporting lemmas in Proofs/"
  IO.println "  6. Complete the proof in ProofOfMainTheorem.lean"
  IO.println "  7. Run 'lake exe tailverify' to verify compliance"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [projectName] =>
    if projectName.startsWith "-" then
      IO.eprintln "Usage: lake exe tailscaffold <ProjectName>"
      IO.eprintln ""
      IO.eprintln "Creates a new Kim Morrison Standard project structure."
      return 1
    try
      scaffold projectName
      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: lake exe tailscaffold <ProjectName>"
    IO.eprintln ""
    IO.eprintln "Creates a new Kim Morrison Standard project structure."
    IO.eprintln ""
    IO.eprintln "The Kim Morrison Standard requires:"
    IO.eprintln "  - MainTheorem.lean imports ONLY from Mathlib"
    IO.eprintln "  - ProofOfMainTheorem.lean uses module system for private imports"
    IO.eprintln "  - StatementOfTheorem : Prop defined in MainTheorem"
    IO.eprintln "  - mainTheorem : StatementOfTheorem proven in ProofOfMainTheorem"
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe tailscaffold MyTheorem"
    return 1

end TAIL.Scaffold

/-- Entry point when run with lake exe -/
def main (args : List String) : IO UInt32 :=
  TAIL.Scaffold.main args
