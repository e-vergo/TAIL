/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Checks.Helpers

/-!
# TAIL Checks - Soundness

Core soundness verification checks:
- Structure check (required declarations exist)
- Soundness check (no sorry, native_decide, trivial True, partial, unsafe)
- Axioms in source (no axiom declarations in source files)
- Unsafe attributes (no implemented_by or extern in source files)
-/

namespace TAIL.Checks

open Lean

/-! ## 1. Structure Check -/

/-- Verify that required declarations exist:
    - `{projectPrefix}.StatementOfTheorem` exists and is a def
    - `{projectPrefix}.mainTheorem` exists in ProofOfMainTheorem module

    Note: In the olean format, theorems imported from other modules appear as axioms.
    This is normal behavior of the Lean module system. -/
def checkStructure (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let statementName := resolved.statementName'
  let theoremName := resolved.theoremName'
  let mainModule := resolved.mainTheoremModule
  let proofModule := resolved.proofOfMainTheoremModule

  -- Find MainTheorem module
  let some mainMod := findModule modules mainModule
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check StatementOfTheorem exists and is a def
  let some statementDecl := findDecl mainMod statementName
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"'{statementName}' not found in MainTheorem module"
        [s!"Expected declaration at fully qualified name: {statementName}"]

  if !statementDecl.kind.isDef then
    return CheckResult.fail CheckCategory.structure "Structure"
      s!"'{statementName}' is a {statementDecl.kind}, expected def"
      ["StatementOfTheorem must be a definition, not a theorem"]

  -- Find ProofOfMainTheorem module
  let some proofMod := findModule modules proofModule
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check mainTheorem exists
  -- Note: In olean, theorems may appear as axioms due to module system
  let some theoremDecl := findDecl proofMod theoremName
    | return CheckResult.fail CheckCategory.structure "Structure"
        s!"'{theoremName}' not found in ProofOfMainTheorem module"
        [s!"Expected theorem at fully qualified name: {theoremName}"]

  -- Accept both theorem and axiom kinds (module system causes theorems to appear as axioms)
  if !theoremDecl.kind.isTheorem && theoremDecl.kind != .ax then
    return CheckResult.fail CheckCategory.structure "Structure"
      s!"'{theoremName}' is a {theoremDecl.kind}, expected theorem"
      ["mainTheorem must be a theorem"]

  return CheckResult.pass CheckCategory.structure "Structure"
    s!"Verified: {statementName} (def), {theoremName} (theorem)"

/-! ## 2. Soundness Check -/

/-- Check if a declaration uses native_decide by looking for Lean.ofReduceBool axiom. -/
def usesNativeDecide (decl : OleanDeclInfo) : Bool :=
  decl.usedConstants.contains ``Lean.ofReduceBool

/-- Comprehensive soundness verification for all project declarations.
    Checks for:
    - sorry (sorryAx in dependencies)
    - native_decide (Lean.ofReduceBool in dependencies)
    - Trivial True (type equals True proposition)
    - partial definitions (DefinitionSafety.partial)
    - unsafe definitions (DefinitionSafety.unsafe)

    Scans all declarations in project modules, skipping auto-generated ones
    but including _private.* declarations. -/
def checkSoundness (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let projectPrefix := resolved.projectPrefix

  let mut violations : Array String := #[]

  -- Check all declarations in all project modules
  for mod in modules do
    -- Only check project modules
    if !mod.name.toString.startsWith projectPrefix then continue

    for decl in mod.declarations do
      -- Skip auto-generated declarations (but NOT _private.*)
      if shouldSkipDeclaration decl.name then continue

      let declModule := mod.name.toString
      let declFullName := s!"{declModule}: {decl.name}"

      -- 1. Check for sorry usage
      if decl.usesSorry then
        violations := violations.push s!"  - {declFullName} (sorry)"

      -- 2. Check for native_decide usage
      if usesNativeDecide decl then
        violations := violations.push s!"  - {declFullName} (native_decide)"

      -- 3. Check for trivial True
      if isTrivialTrue decl.type then
        violations := violations.push s!"  - {declFullName} (trivial True)"

      -- 4. Check for partial definitions
      if decl.safety == some .partial then
        violations := violations.push s!"  - {declFullName} (partial def - non-termination risk)"

      -- 5. Check for unsafe definitions
      if decl.safety == some .unsafe then
        violations := violations.push s!"  - {declFullName} (unsafe - bypasses type checker)"

  -- Build result
  if violations.isEmpty then
    return CheckResult.pass CheckCategory.soundness "Soundness"
      "No soundness violations detected"
  else
    return CheckResult.fail CheckCategory.soundness "Soundness"
      s!"Found {violations.size} soundness violation(s)"
      violations.toList

/-! ## 2b. Source-Based Axiom Check -/

/-- Check if a trimmed line contains an axiom declaration.
    Returns (isAxiom, axiomDeclaration) where axiomDeclaration is the full line text if it's an axiom. -/
private def isAxiomLine (line : String) : Bool × String :=
  let trimmed := line.trimAscii.toString
  -- Check for "axiom " or "private axiom " at the start
  if trimmed.startsWith "axiom " then
    (true, trimmed)
  else if trimmed.startsWith "private axiom " then
    (true, trimmed)
  else
    (false, "")

/-- Check if a line is inside a comment (basic heuristic).
    Returns true if the line contains "--" before any potential axiom keyword. -/
private def isCommentedOut (line : String) : Bool :=
  match line.splitOn "--" with
  | [] => false
  | [_] => false  -- No "--" found
  | beforeComment :: _ =>
    -- Check if "axiom" appears before the comment marker
    !(beforeComment.contains "axiom")

/-- Scan all .lean files in the project source directory for axiom declarations.
    Reports file path, line number, and axiom declaration for each violation. -/
def checkAxiomsInSource (resolved : ResolvedConfig) : IO CheckResult := do
  let leanFiles ← TAIL.discoverLeanFiles resolved.sourcePath
  let mut violations : Array String := #[]

  for filePath in leanFiles do
    let content ← IO.FS.readFile filePath
    let lines := content.splitOn "\n"

    let mut lineNumber := 0
    for line in lines do
      lineNumber := lineNumber + 1

      -- Skip commented lines
      if isCommentedOut line then continue

      let (isAxiom, axiomDecl) := isAxiomLine line
      if isAxiom then
        -- Get relative path from project root for cleaner output
        let relPath := filePath.toString.replace (resolved.projectRoot.toString ++ "/") ""
        violations := violations.push s!"  - {relPath}:{lineNumber}: {axiomDecl}"

  if violations.isEmpty then
    return CheckResult.pass CheckCategory.soundness "Axioms in Source"
      "No axiom declarations found in source files"
  else
    return CheckResult.fail CheckCategory.soundness "Axioms in Source"
      s!"Found {violations.size} axiom declaration(s) in source files"
      violations.toList

/-! ## 2c. Unsafe Attributes Check -/

/-- Check if a trimmed line contains an unsafe attribute.
    Returns (hasUnsafe, attributeName, fullLine). -/
private def isUnsafeAttributeLine (line : String) : Bool × String × String :=
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "@[implemented_by" then
    (true, "implemented_by", trimmed)
  else if trimmed.startsWith "@[extern" then
    (true, "extern", trimmed)
  else
    (false, "", "")

/-- Scan all .lean files for unsafe attributes that bypass kernel verification.
    Reports file path, line number, and attribute for each violation. -/
def checkUnsafeAttributesInSource (resolved : ResolvedConfig) : IO CheckResult := do
  let leanFiles ← TAIL.discoverLeanFiles resolved.sourcePath
  let mut violations : Array String := #[]

  for filePath in leanFiles do
    let content ← IO.FS.readFile filePath
    let lines := content.splitOn "\n"

    let mut lineNumber := 0
    for line in lines do
      lineNumber := lineNumber + 1

      -- Skip if line starts with comment
      let trimmed := line.trimAscii.toString
      if trimmed.startsWith "--" then continue

      let (hasUnsafe, attrName, fullLine) := isUnsafeAttributeLine line
      if hasUnsafe then
        let relPath := filePath.toString.replace (resolved.projectRoot.toString ++ "/") ""
        violations := violations.push s!"  - {relPath}:{lineNumber}: {attrName} ({fullLine})"

  if violations.isEmpty then
    return CheckResult.pass CheckCategory.soundness "Unsafe Attributes"
      "No implemented_by or extern attributes found"
  else
    return CheckResult.fail CheckCategory.soundness "Unsafe Attributes"
      s!"Found {violations.size} unsafe attribute(s) in source files"
      violations.toList

/-! ## 2d. Opaque Declarations Check -/

/-- Check if a trimmed line contains an opaque declaration.
    Returns (isOpaque, declaration) where declaration is the line text. -/
private def isOpaqueLine (line : String) : Bool × String :=
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "opaque " then
    (true, trimmed)
  else if trimmed.startsWith "private opaque " then
    (true, trimmed)
  else
    (false, "")

/-- Scan all .lean files for opaque declarations.
    Reports file path, line number, and declaration for each violation. -/
def checkOpaquesInSource (resolved : ResolvedConfig) : IO CheckResult := do
  let leanFiles ← TAIL.discoverLeanFiles resolved.sourcePath
  let mut violations : Array String := #[]

  for filePath in leanFiles do
    let content ← IO.FS.readFile filePath
    let lines := content.splitOn "\n"

    let mut lineNumber := 0
    for line in lines do
      lineNumber := lineNumber + 1

      -- Skip if line starts with comment
      let trimmed := line.trimAscii.toString
      if trimmed.startsWith "--" then continue

      let (isOpaque, opaqueDecl) := isOpaqueLine line
      if isOpaque then
        let relPath := filePath.toString.replace (resolved.projectRoot.toString ++ "/") ""
        violations := violations.push s!"  - {relPath}:{lineNumber}: {opaqueDecl}"

  if violations.isEmpty then
    return CheckResult.pass CheckCategory.soundness "Opaques in Source"
      "No opaque declarations found in source files"
  else
    return CheckResult.fail CheckCategory.soundness "Opaques in Source"
      s!"Found {violations.size} opaque declaration(s) in source files"
      violations.toList

end TAIL.Checks
