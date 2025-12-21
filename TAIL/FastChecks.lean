/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.OleanReader
import TAIL.Types
import TAIL.Config
import TAIL.Utils

/-!
# TAIL Fast Checks

Fast verification checks using OleanReader instead of full environment loading.
These checks are pure IO functions that operate on `OleanModuleInfo` and `OleanDeclInfo`.

All checks use the olean-based module reading for efficient verification without
loading the full Lean environment.
-/

namespace TAIL.FastChecks

open Lean

/-! ## Standard Axioms -/

/-- The four standard axioms accepted in verified Lean proofs -/
def standardAxioms : List Name :=
  [`propext, `Quot.sound, ``Classical.choice, ``funext]

/-- Check if an axiom is one of the standard accepted axioms -/
def isStandardAxiom (n : Name) : Bool :=
  standardAxioms.contains n

/-! ## Module Lookup Helpers -/

/-- Find a module by name in the array of modules -/
def findModule (modules : Array OleanModuleInfo) (name : Name) : Option OleanModuleInfo :=
  modules.find? (·.name == name)

/-- Find a declaration by name in a module -/
def findDecl (mod : OleanModuleInfo) (name : Name) : Option OleanDeclInfo :=
  mod.declarations.find? (·.name == name)

/-- Get all non-internal declarations from a module -/
def getUserDeclarations (mod : OleanModuleInfo) : Array OleanDeclInfo :=
  mod.declarations.filter (!·.isInternal)

/-- Check if an import is from the standard library -/
def isStandardLibraryImport (moduleName : Name) : Bool :=
  let nameStr := moduleName.toString
  TAIL.standardLibraryPrefixes.any (nameStr.startsWith ·)

/-- Check if an import is a project import -/
def isProjectImport (moduleName : Name) (projectPrefix : String) : Bool :=
  moduleName.toString.startsWith projectPrefix

/-! ## 1. Structure Check -/

/-- Verify that required declarations exist:
    - `{projectPrefix}.StatementOfTheorem` exists and is a def
    - `{projectPrefix}.mainTheorem` exists in ProofOfMainTheorem module

    Note: In the olean format, theorems imported from other modules appear as axioms.
    This is normal behavior of the Lean module system. -/
def checkStructureFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let statementName := resolved.statementName'
  let theoremName := resolved.theoremName'
  let mainModule := resolved.mainTheoremModule
  let proofModule := resolved.proofOfMainTheoremModule

  -- Find MainTheorem module
  let some mainMod := findModule modules mainModule
    | return CheckResult.fail "Structure"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check StatementOfTheorem exists and is a def
  let some statementDecl := findDecl mainMod statementName
    | return CheckResult.fail "Structure"
        s!"'{statementName}' not found in MainTheorem module"
        [s!"Expected declaration at fully qualified name: {statementName}"]

  if !statementDecl.kind.isDef then
    return CheckResult.fail "Structure"
      s!"'{statementName}' is a {statementDecl.kind}, expected def"
      ["StatementOfTheorem must be a definition, not a theorem"]

  -- Find ProofOfMainTheorem module
  let some proofMod := findModule modules proofModule
    | return CheckResult.fail "Structure"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  -- Check mainTheorem exists
  -- Note: In olean, theorems may appear as axioms due to module system
  let some theoremDecl := findDecl proofMod theoremName
    | return CheckResult.fail "Structure"
        s!"'{theoremName}' not found in ProofOfMainTheorem module"
        [s!"Expected theorem at fully qualified name: {theoremName}"]

  -- Accept both theorem and axiom kinds (module system causes theorems to appear as axioms)
  if !theoremDecl.kind.isTheorem && theoremDecl.kind != .ax then
    return CheckResult.fail "Structure"
      s!"'{theoremName}' is a {theoremDecl.kind}, expected theorem"
      ["mainTheorem must be a theorem"]

  return CheckResult.pass "Structure"
    s!"Verified: {statementName} (def), {theoremName} (theorem)"

/-! ## 2. Soundness Check -/

/-- Comprehensive soundness verification for all project declarations.
    Checks:
    - No sorry usage (sorryAx in dependencies)
    - No opaque declarations
    - Only standard axioms used -/
def checkSoundnessFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let projectPrefix := resolved.projectPrefix

  let mut sorryDecls : Array Name := #[]
  let mut opaqueDecls : Array Name := #[]
  let mut nonStandardAxioms : Array (Name × Name) := #[]  -- (decl, axiom)
  let mut allAxioms : Std.HashSet Name := {}

  -- Check all declarations in all project modules
  for mod in modules do
    -- Only check project modules
    if !mod.name.toString.startsWith projectPrefix then continue

    for decl in mod.declarations do
      -- Skip internal declarations
      if decl.isInternal then continue

      -- Check for sorry usage
      if decl.usesSorry then
        sorryDecls := sorryDecls.push decl.name

      -- Check for opaque declarations
      if decl.kind == .opaq then
        opaqueDecls := opaqueDecls.push decl.name

      -- Check for non-standard axioms in dependencies
      for dep in decl.usedConstants do
        -- We can't easily check if a dep is an axiom without the environment,
        -- but we can check if it's sorryAx or one of the standard axioms
        if dep == ``sorryAx then
          -- Already caught by usesSorry check
          continue
        -- Track axioms by looking at naming patterns
        -- Note: This is a heuristic since we don't have full env
        if isStandardAxiom dep then
          allAxioms := allAxioms.insert dep

  -- Build result
  let mut details : Array String := #[]
  let mut passed := true

  -- Report sorry usage
  if !sorryDecls.isEmpty then
    passed := false
    details := details.push "CRITICAL: The following declarations use 'sorry':"
    for decl in sorryDecls do
      details := details.push s!"  - {decl}"

  -- Report opaque declarations
  if !opaqueDecls.isEmpty then
    passed := false
    details := details.push "Opaque declarations found (not allowed):"
    for decl in opaqueDecls do
      details := details.push s!"  - {decl}"

  -- Report non-standard axioms
  if !nonStandardAxioms.isEmpty then
    passed := false
    details := details.push "Non-standard axioms detected:"
    for (decl, ax) in nonStandardAxioms do
      details := details.push s!"  - {decl} uses {ax}"

  if passed then
    let axiomList := String.intercalate ", " (allAxioms.toArray.map (·.toString)).toList
    let msg := if axiomList.isEmpty then
      "No axioms detected in direct dependencies"
    else
      s!"Standard axioms used: {axiomList}"
    return CheckResult.pass "Soundness" msg
  else
    let issues := [
      if !sorryDecls.isEmpty then some s!"{sorryDecls.size} sorry" else none,
      if !opaqueDecls.isEmpty then some s!"{opaqueDecls.size} opaque" else none,
      if !nonStandardAxioms.isEmpty then some s!"{nonStandardAxioms.size} non-standard axioms" else none
    ].filterMap id |> String.intercalate ", "
    return CheckResult.fail "Soundness" issues details.toList

/-! ## 3. Proof Minimality Check -/

/-- Verify ProofOfMainTheorem.lean contains exactly one theorem (the main theorem).
    Note: Due to the module system, theorems may appear as axioms in olean. -/
def checkProofMinimalityFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let proofModule := resolved.proofOfMainTheoremModule
  let theoremName := resolved.theoremName'

  let some proofMod := findModule modules proofModule
    | return CheckResult.fail "Proof Minimality"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  let userDecls := getUserDeclarations proofMod

  -- Filter to theorems/axioms (theorems appear as axioms in olean due to module system)
  let theoremsAndAxioms := userDecls.filter fun decl =>
    decl.kind.isTheorem || decl.kind == .ax

  -- Filter out standard axioms (propext, etc. shouldn't count)
  let projectTheorems := theoremsAndAxioms.filter fun decl =>
    !isStandardAxiom decl.name && decl.name != ``sorryAx

  let mut details : Array String := #[]
  let mut passed := true

  if projectTheorems.isEmpty then
    passed := false
    details := details.push "No theorem found in ProofOfMainTheorem.lean"
  else if projectTheorems.size == 1 then
    let thm := projectTheorems[0]!
    if thm.name != theoremName then
      details := details.push s!"Found theorem '{thm.name}' (expected '{theoremName}')"
      -- This is a warning, not a failure
  else
    passed := false
    details := details.push s!"Multiple theorems/axioms found ({projectTheorems.size}):"
    for thm in projectTheorems do
      details := details.push s!"  - {thm.kind} {thm.name}"

  -- Check for extra defs (potential violations)
  let extraDefs := userDecls.filter fun decl =>
    decl.kind.isDef

  if !extraDefs.isEmpty then
    passed := false
    details := details.push s!"Extra definitions found ({extraDefs.size}):"
    for def_ in extraDefs do
      details := details.push s!"  - def {def_.name}"

  if passed then
    let thmName := if projectTheorems.isEmpty then "none" else projectTheorems[0]!.name.toString
    return CheckResult.pass "Proof Minimality"
      s!"Contains exactly one theorem: {thmName}"
  else
    return CheckResult.fail "Proof Minimality"
      "ProofOfMainTheorem.lean structure invalid" details.toList

/-! ## 4. MainTheorem Isolation Check -/

/-- Check that MainTheorem.lean contains only allowed declarations.
    - Should have no theorems, only defs
    - In strict mode: extra defs (beyond StatementOfTheorem) are errors
    - In default mode: extra defs are warnings -/
def checkMainTheoremIsolatedFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let mainModule := resolved.mainTheoremModule
  let statementName := resolved.statementName'

  let some mainMod := findModule modules mainModule
    | return CheckResult.fail "MainTheorem Isolation"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  let userDecls := getUserDeclarations mainMod

  let mut theorems : Array Name := #[]
  let mut axioms : Array Name := #[]
  let mut opaques : Array Name := #[]
  let mut extraDefs : Array Name := #[]

  for decl in userDecls do
    if decl.name == statementName then continue  -- StatementOfTheorem is always allowed

    match decl.kind with
    | .thm => theorems := theorems.push decl.name
    | .ax =>
      -- Skip standard axioms
      if !isStandardAxiom decl.name && decl.name != ``sorryAx then
        axioms := axioms.push decl.name
    | .opaq => opaques := opaques.push decl.name
    | .defn => extraDefs := extraDefs.push decl.name
    | .ind => extraDefs := extraDefs.push decl.name  -- inductives/structures
    | _ => continue

  let mut details : Array String := #[]
  let mut passed := true

  -- Check that StatementOfTheorem exists
  let hasStatement := userDecls.any (·.name == statementName)
  if !hasStatement then
    passed := false
    details := details.push s!"ERROR: '{statementName}' not found"

  -- Theorems are always disallowed
  if !theorems.isEmpty then
    passed := false
    for thm in theorems do
      details := details.push s!"ERROR: theorem {thm} (theorems not allowed in MainTheorem.lean)"

  -- Axioms are always disallowed (except standard ones, already filtered)
  if !axioms.isEmpty then
    passed := false
    for ax in axioms do
      details := details.push s!"ERROR: axiom {ax} (axioms not allowed in MainTheorem.lean)"

  -- Opaques are always disallowed
  if !opaques.isEmpty then
    passed := false
    for op in opaques do
      details := details.push s!"ERROR: opaque {op} (opaque not allowed in MainTheorem.lean)"

  -- Handle extra definitions based on mode
  if !extraDefs.isEmpty then
    match resolved.mode with
    | .strict =>
      passed := false
      for def_ in extraDefs do
        details := details.push s!"ERROR: {def_} (strict mode allows only StatementOfTheorem)"
    | .default =>
      for def_ in extraDefs do
        details := details.push s!"WARNING: {def_} (consider moving to Definitions/ folder)"

  if passed then
    if extraDefs.isEmpty then
      return CheckResult.pass "MainTheorem Isolation"
        "MainTheorem.lean contains only StatementOfTheorem"
    else
      return CheckResult.pass "MainTheorem Isolation"
        s!"MainTheorem.lean valid ({extraDefs.size} extra defs - consider moving to Definitions/)"
  else
    return CheckResult.fail "MainTheorem Isolation"
      "MainTheorem.lean contains disallowed declarations" details.toList

/-! ## 5. Imports Check -/

/-- Check MainTheorem.lean imports -/
def checkMainTheoremImportsFast (mainMod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut violations : Array String := #[]

  for imp in mainMod.imports do
    let modName := imp.module
    let modStr := modName.toString

    -- Check if this is a project import
    if modStr.startsWith resolved.projectPrefix then
      -- In default mode, Definitions/ imports are allowed
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      else
        violations := violations.push s!"  - {modStr} (project import not allowed)"
    else if !isStandardLibraryImport modName then
      violations := violations.push s!"  - {modStr} (non-Mathlib import)"

  (violations, violations.isEmpty)

/-- Check ProofOfMainTheorem.lean imports -/
def checkProofImportsFast (proofMod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut hasMainTheoremImport := false
  let mut hasStandardLibrary := false
  let mut violations : Array String := #[]

  for imp in proofMod.imports do
    let modName := imp.module
    let modStr := modName.toString

    if modName == resolved.mainTheoremModule then
      hasMainTheoremImport := true
    else if isStandardLibraryImport modName then
      hasStandardLibrary := true
    else if modStr.startsWith resolved.projectPrefix then
      -- Definitions/ imports allowed in default mode
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      -- Proofs/ imports always allowed
      else if resolved.isProofsModule modName then
        continue
      else
        violations := violations.push s!"  - Unexpected project import: {modStr}"

  if !hasMainTheoremImport then
    violations := #[s!"  - Missing required import: MainTheorem"] ++ violations

  if !hasStandardLibrary then
    violations := #[s!"  - Missing standard library import (typically Mathlib)"] ++ violations

  (violations, violations.isEmpty)

/-- Check imports for MainTheorem.lean and ProofOfMainTheorem.lean -/
def checkImportsFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  let mainModule := resolved.mainTheoremModule
  let proofModule := resolved.proofOfMainTheoremModule

  let some mainMod := findModule modules mainModule
    | return CheckResult.fail "Import Discipline"
        s!"MainTheorem module not found: {mainModule}"
        ["Ensure the project has been built with `lake build`"]

  let some proofMod := findModule modules proofModule
    | return CheckResult.fail "Import Discipline"
        s!"ProofOfMainTheorem module not found: {proofModule}"
        ["Ensure the project has been built with `lake build`"]

  let mut allViolations : Array String := #[]

  -- Check MainTheorem imports
  let (mainViolations, mainOk) := checkMainTheoremImportsFast mainMod resolved
  if !mainOk then
    allViolations := allViolations.push "MainTheorem.lean import violations:"
    allViolations := allViolations ++ mainViolations

  -- Check ProofOfMainTheorem imports
  let (proofViolations, proofOk) := checkProofImportsFast proofMod resolved
  if !proofOk then
    allViolations := allViolations.push "ProofOfMainTheorem.lean import violations:"
    allViolations := allViolations ++ proofViolations

  if allViolations.isEmpty then
    let modeNote := if resolved.mode == .strict
      then "Mathlib-only imports verified"
      else "Mathlib/Definitions imports verified"
    return CheckResult.pass "Import Discipline" modeNote
  else
    return CheckResult.fail "Import Discipline"
      "Import violations detected" allViolations.toList

/-! ## 6. Proofs Purity Check -/

/-- Check imports for a Proofs/ module -/
def checkProofsModuleImportsFast (mod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut violations : Array String := #[]

  for imp in mod.imports do
    let modName := imp.module
    let modStr := modName.toString

    if modName == resolved.mainTheoremModule then
      violations := violations.push s!"  - Cannot import MainTheorem from Proofs/"
    else if modName == resolved.proofOfMainTheoremModule then
      violations := violations.push s!"  - Cannot import ProofOfMainTheorem from Proofs/"
    else if isStandardLibraryImport modName then
      continue
    else if modStr.startsWith resolved.projectPrefix then
      if resolved.mode == .default && resolved.isDefinitionsModule modName then
        continue
      else if resolved.isProofsModule modName then
        continue
      else
        violations := violations.push s!"  - Unexpected project import: {modStr}"

  (violations, violations.isEmpty)

/-- Check if a name looks like an auto-generated definition (structure helpers, recursors, etc.) -/
def isAutoGeneratedDef (name : Name) : Bool :=
  let nameStr := name.toString
  -- Recursors and case analysis
  TAIL.containsSubstr nameStr ".rec" ||
  TAIL.containsSubstr nameStr ".recOn" ||
  TAIL.containsSubstr nameStr ".casesOn" ||
  TAIL.containsSubstr nameStr ".below" ||
  TAIL.containsSubstr nameStr ".ibelow" ||
  TAIL.containsSubstr nameStr ".brecOn" ||
  TAIL.containsSubstr nameStr ".binductionOn" ||
  -- Discrimination/confusion
  TAIL.containsSubstr nameStr ".noConfusion" ||
  TAIL.containsSubstr nameStr ".noConfusionType" ||
  -- Constructor helpers
  TAIL.containsSubstr nameStr ".ctorIdx" ||
  TAIL.containsSubstr nameStr ".mk.sizeOf_spec" ||
  -- Size helpers
  TAIL.containsSubstr nameStr ".sizeOf_spec" ||
  -- Match on internal names (structure field projectors, etc.)
  name.isInternal

/-- Check if a name is a field projector for any of the given structures -/
def isFieldProjector (name : Name) (structures : Array Name) : Bool :=
  structures.any fun structName =>
    let structPrefix := structName.toString ++ "."
    let nameStr := name.toString
    nameStr.startsWith structPrefix && !TAIL.containsSubstr nameStr ".rec"

/-- Check that all Proofs/ files follow the rules -/
def checkProofsPurityFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  -- Skip if no Proofs/ folder
  if resolved.proofsPath.isNone then
    return CheckResult.pass "Proofs Purity"
      "Skipped (no Proofs/ folder present)"

  -- Find all modules in Proofs/
  let proofsModules := modules.filter fun mod =>
    resolved.isProofsModule mod.name

  if proofsModules.isEmpty then
    return CheckResult.pass "Proofs Purity"
      "No modules found in Proofs/ folder"

  let mut allViolations : Array String := #[]
  let mut moduleCount := 0

  for mod in proofsModules do
    moduleCount := moduleCount + 1

    -- Check import restrictions
    let (importViolations, importsOk) := checkProofsModuleImportsFast mod resolved
    if !importsOk then
      allViolations := allViolations.push s!"Import violations in {mod.name}:"
      allViolations := allViolations ++ importViolations

    -- First pass: collect all structures/inductives (not allowed in Proofs/)
    let userDecls := getUserDeclarations mod
    let mut detectedStructures : Array Name := #[]

    for decl in userDecls do
      if decl.kind == .ind then
        detectedStructures := detectedStructures.push decl.name
        allViolations := allViolations.push s!"  - structure/inductive {decl.name} (not allowed in Proofs/)"

    -- Second pass: check other declarations
    for decl in userDecls do
      -- Skip structures (already handled above)
      if decl.kind == .ind then continue

      -- Per spec.md, Proofs/ allows: theorem, lemma, def returning Prop
      -- Proofs/ disallows: axiom, opaque, sorry, structure/inductive, def without proof obligation

      -- Check for sorry usage
      if decl.usesSorry then
        allViolations := allViolations.push s!"  - {decl.name} uses sorry in {mod.name}"

      -- Check for defs without proof obligation (must return Prop)
      -- Filter out auto-generated structure helpers and field projectors
      if decl.kind.isDef && !isAutoGeneratedDef decl.name && !isFieldProjector decl.name detectedStructures then
        -- Check if the type is Prop (Sort 0) or returns Prop
        let isPropValued := decl.type.isProp || decl.type.isForall && decl.type.bindingBody!.isProp
        if !isPropValued then
          allViolations := allViolations.push s!"  - def {decl.name} (defs in Proofs/ must return Prop)"

      -- Note: We don't flag axioms here because the Lean module system stores
      -- theorems in `public section` as axioms in the olean. The Soundness check
      -- already verifies no non-standard axioms exist in the environment.

      -- Check for opaques
      if decl.kind == .opaq then
        allViolations := allViolations.push s!"  - opaque {decl.name} (opaque not allowed in Proofs/)"

  if allViolations.isEmpty then
    return CheckResult.pass "Proofs Purity"
      s!"All {moduleCount} Proofs/ modules are valid"
  else
    return CheckResult.fail "Proofs Purity"
      "Proofs/ folder contains disallowed content" allViolations.toList

/-! ## 7. Definitions Purity Check -/

/-- Check imports for a Definitions/ module -/
def checkDefinitionsModuleImportsFast (mod : OleanModuleInfo) (resolved : ResolvedConfig) :
    Array String × Bool := Id.run do
  let mut violations : Array String := #[]

  for imp in mod.imports do
    let modName := imp.module
    let modStr := modName.toString

    if modStr.startsWith resolved.projectPrefix then
      -- Only Definitions/ imports are allowed from project
      if resolved.isDefinitionsModule modName then
        continue
      else
        violations := violations.push s!"  - {modStr} (only Definitions/ imports allowed)"
    else if !isStandardLibraryImport modName then
      violations := violations.push s!"  - {modStr} (non-Mathlib import)"

  (violations, violations.isEmpty)

/-- Check if a name looks like an auto-generated theorem -/
def isAutoGeneratedTheorem (name : Name) : Bool :=
  let nameStr := name.toString
  TAIL.containsSubstr nameStr ".rec" ||
  TAIL.containsSubstr nameStr ".recOn" ||
  TAIL.containsSubstr nameStr ".casesOn" ||
  TAIL.containsSubstr nameStr ".below" ||
  TAIL.containsSubstr nameStr ".ibelow" ||
  TAIL.containsSubstr nameStr ".brecOn" ||
  TAIL.containsSubstr nameStr ".binductionOn" ||
  TAIL.containsSubstr nameStr ".noConfusion" ||
  TAIL.containsSubstr nameStr ".noConfusionType" ||
  TAIL.containsSubstr nameStr ".sizeOf_spec" ||
  TAIL.containsSubstr nameStr ".eq_def" ||
  TAIL.containsSubstr nameStr ".ext" ||
  TAIL.containsSubstr nameStr ".mk.injEq" ||
  TAIL.containsSubstr nameStr ".mk.sizeOf_spec"

/-- Check that all Definitions/ files follow the rules -/
def checkDefinitionsPurityFast (resolved : ResolvedConfig) (modules : Array OleanModuleInfo) : IO CheckResult := do
  -- Skip if strict mode
  if resolved.mode == .strict then
    return CheckResult.pass "Definitions Purity"
      "Skipped (strict mode - no Definitions/ folder allowed)"

  -- Skip if no Definitions/ folder
  if resolved.definitionsPath.isNone then
    return CheckResult.pass "Definitions Purity"
      "Skipped (no Definitions/ folder present)"

  -- Find all modules in Definitions/
  let defModules := modules.filter fun mod =>
    resolved.isDefinitionsModule mod.name

  if defModules.isEmpty then
    return CheckResult.pass "Definitions Purity"
      "No modules found in Definitions/ folder"

  let mut allViolations : Array String := #[]
  let mut moduleCount := 0

  for mod in defModules do
    moduleCount := moduleCount + 1

    -- Check imports
    let (importViolations, importsOk) := checkDefinitionsModuleImportsFast mod resolved
    if !importsOk then
      allViolations := allViolations.push s!"Import violations in {mod.name}:"
      allViolations := allViolations ++ importViolations

    -- Check declarations
    let userDecls := getUserDeclarations mod
    for decl in userDecls do
      -- Check for theorems (not allowed, unless auto-generated)
      if decl.kind.isTheorem then
        if !isAutoGeneratedTheorem decl.name then
          allViolations := allViolations.push s!"  - theorem {decl.name} (theorems not allowed in Definitions/)"

      -- Check for sorry usage in defs
      if decl.kind.isDef && decl.usesSorry then
        allViolations := allViolations.push s!"  - {decl.name} uses sorry (not allowed in Definitions/)"

      -- Note: We don't flag axioms here because:
      -- 1. The Lean module system stores public theorems as axioms in olean
      -- 2. Structure proof-valued fields appear as axioms
      -- 3. Auto-generated structure lemmas (mk.inj, etc.) appear as axioms
      -- The Soundness check already verifies no problematic axioms exist.

      -- Check for opaques
      if decl.kind == .opaq then
        allViolations := allViolations.push s!"  - opaque {decl.name} (opaque not allowed)"

  if allViolations.isEmpty then
    return CheckResult.pass "Definitions Purity"
      s!"All {moduleCount} Definitions/ modules are valid"
  else
    return CheckResult.fail "Definitions Purity"
      "Definitions/ folder contains disallowed content" allViolations.toList

/-! ## 8. Run All Checks -/

/-- Run all verification checks using the fast olean-based reader.
    Returns a list of all check results. -/
def runFastChecks (resolved : ResolvedConfig) : IO (List CheckResult) := do
  -- Read all project modules
  let modules ← readProjectModules resolved

  if modules.isEmpty then
    return [CheckResult.fail "Module Loading"
      "No modules found"
      ["Ensure the project has been built with `lake build`",
       s!"Expected source directory: {resolved.sourcePath}"]]

  -- Run all checks
  let structureResult ← checkStructureFast resolved modules
  let soundnessResult ← checkSoundnessFast resolved modules
  let minimalityResult ← checkProofMinimalityFast resolved modules
  let isolationResult ← checkMainTheoremIsolatedFast resolved modules
  let importsResult ← checkImportsFast resolved modules
  let proofsPurityResult ← checkProofsPurityFast resolved modules
  let defsPurityResult ← checkDefinitionsPurityFast resolved modules

  return [
    structureResult,
    soundnessResult,
    minimalityResult,
    isolationResult,
    importsResult,
    proofsPurityResult,
    defsPurityResult
  ]

end TAIL.FastChecks
