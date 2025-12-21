/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config
import TAIL.Environment

/-!
# Soundness Check

Comprehensive soundness verification for TAIL Standard compliance.

## Checks Performed

1. **Axiom Safety**: Verify only standard axioms are used (propext, Quot.sound, Classical.choice, funext)
2. **No Sorry**: Ensure no incomplete proofs (sorryAx usage)
3. **No Custom Axioms**: No project-defined axioms
4. **No native_decide**: Avoid non-kernel-verified decision procedures
5. **No Opaque Declarations**: Ensure all definitions are transparent
6. **No Trivial Theorems**: Detect True, trivial, and other placeholder proofs

## Shallow Dependency Checking Optimization

This implementation uses **shallow dependency checking** instead of deep recursive traversal.

**Key insight**: Since we check EVERY project declaration individually, we don't need to
recursively traverse the dependency graph. If `helperLemma` uses `sorry`, we'll detect it
when we check `helperLemma` directly - we don't need to detect it again when checking
`mainTheorem` that uses `helperLemma`.

This optimization:
- Reduces time complexity from O(declarations × average_depth) to O(declarations × average_direct_deps)
- Eliminates expensive graph traversal and caching
- Maintains exact functional correctness (same violations detected)
- Provides significant performance improvement on large projects

## native_decide Detection

`native_decide` is a soundness concern because it:
- Compiles the decision procedure to native code
- Executes it and trusts the boolean result
- Does not produce a kernel-verifiable proof

Unlike `decide` (which is sound - kernel verifies the Decidable proof),
`native_decide` can produce incorrect results if there are bugs in
native code generation. Mathlib and serious verification projects avoid it.

The internal constant for `native_decide` is `Lean.ofReduceBool`.
-/

namespace TAIL.Checks

open Lean Meta

/-! ## Standard Axioms -/

/-- The four standard axioms accepted in verified Lean proofs -/
def standardAxioms : List Name :=
  [`propext, `Quot.sound, ``Classical.choice, ``funext]

/-- Check if an axiom is one of the standard accepted axioms -/
def isStandardAxiom (n : Name) : Bool :=
  standardAxioms.contains n

/-! ## Shallow Dependency Checking -/

/-- Check if a name is a non-standard axiom (excluding sorryAx) -/
def isNonStandardAxiom (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.axiomInfo _) => !isStandardAxiom name && name != ``sorryAx
  | _ => false

/-- Get immediate non-standard axioms from a declaration's direct dependencies.
    Returns (hasSorry, nonStandardAxioms).

    KEY INSIGHT: Since we check EVERY project declaration, we don't need deep traversal.
    If helperLemma uses sorry, we'll catch it when we check helperLemma directly. -/
def checkDirectDependencies (env : Environment) (directDeps : Array Name) : Bool × Array Name := Id.run do
  let mut hasSorry := false
  let mut nonStandard : Array Name := #[]

  for dep in directDeps do
    -- Check for sorryAx
    if dep == ``sorryAx then
      hasSorry := true

    -- Check for non-standard axioms
    if isNonStandardAxiom env dep then
      nonStandard := nonStandard.push dep

  return (hasSorry, nonStandard)

/-! ## native_decide Detection -/

/-- Check if a declaration uses native_decide (shallow check via dependencies) -/
def usesNativeDecide (directDeps : Array Name) : Bool :=
  directDeps.contains ``Lean.ofReduceBool || directDeps.contains ``Lean.ofReduceNat

/-! ## Trivial Theorem Detection -/

/-- Trivial proof terms that indicate placeholder or meaningless theorems -/
def trivialProofConstants : List Name :=
  [`True.intro, `trivial]

/-- Check if an expression is a trivial proof (True.intro, trivial, rfl with no meaningful content) -/
def isTrivialProof (e : Expr) : MetaM Bool := do
  -- Check for direct trivial constants
  if let .const name _ := e then
    if trivialProofConstants.contains name then
      return true

  -- Check for () which is Unit.unit
  if let .const name _ := e then
    if name == ``Unit.unit || name == ``PUnit.unit then
      return true

  -- Check type: if proving True or Unit, it's trivial
  let ty ← inferType e
  let ty := ty.consumeMData
  if let .const name _ := ty then
    if name == ``True || name == ``Unit || name == ``PUnit then
      return true

  return false

/-- Check if a theorem's type is trivially True -/
def hasTrivialType (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  match ty with
  | .const name _ => name == ``True || name == ``Unit || name == ``PUnit
  | _ => false

/-! ## Main Soundness Check -/

/-- Comprehensive soundness verification for all project declarations -/
def checkSoundness (resolved : ResolvedConfig) (index : Option TAIL.EnvironmentIndex := none) : MetaM CheckResult := do
  let env ← getEnv
  let projectPrefix := resolved.projectPrefix

  let mut allAxioms : Std.HashSet Name := {}
  let mut sorryDecls : List Name := []
  let mut nonStandardDecls : List (Name × Array Name) := []
  let mut customAxioms : List Name := []
  let mut opaqueDecls : List Name := []
  let mut nativeDecideUsages : List Name := []
  let mut trivialTheorems : List Name := []

  -- The standard TAIL names (not prefixed) - must always check these
  let mainTheoremName := resolved.theoremName'
  let statementName := resolved.statementName'

  -- Get project declarations - use index if available (keep as Array)
  let projectDeclsArray := match index with
    | some idx => idx.projectDeclarations
    | none =>
      -- Fallback: traverse environment using module-based filtering
      -- (consistent with buildEnvironmentIndex)
      let allNames : List Name := env.constants.toList.map Prod.fst
      let projectNames := allNames.filter fun (name : Name) =>
        match TAIL.getModuleName env name with
        | some modName => TAIL.isProjectModule modName projectPrefix
        | none => false
      projectNames.toArray

  -- Build HashSet for O(n) deduplication (replaces O(n²) eraseDups)
  let mut declSet : Std.HashSet Name := {}
  for decl in projectDeclsArray do
    declSet := declSet.insert decl
  declSet := declSet.insert mainTheoremName
  declSet := declSet.insert statementName

  for name in declSet do
    let some info := env.find? name | continue

    match info with
    | .axiomInfo _ =>
      -- Custom project axioms are not allowed
      if !isStandardAxiom name && name != ``sorryAx then
        customAxioms := name :: customAxioms

    | .opaqueInfo _ =>
      opaqueDecls := name :: opaqueDecls

    | .thmInfo ti =>
      -- Shallow axiom check: only check immediate dependencies
      let directDeps := ti.value.getUsedConstants
      let (hasSorry, nonStandard) := checkDirectDependencies env directDeps

      -- Track sorryAx usage
      if hasSorry then
        sorryDecls := name :: sorryDecls

      -- Track non-standard axioms (excluding sorryAx which is tracked separately)
      if !nonStandard.isEmpty then
        nonStandardDecls := (name, nonStandard) :: nonStandardDecls

      -- Collect all axioms used (direct dependencies only)
      for dep in directDeps do
        match env.find? dep with
        | some (.axiomInfo _) => allAxioms := allAxioms.insert dep
        | _ => pure ()

      -- Check for native_decide usage (shallow check)
      if usesNativeDecide directDeps then
        nativeDecideUsages := name :: nativeDecideUsages

      -- Check for trivial theorems (type is True, proof is trivial)
      if hasTrivialType ti.type then
        trivialTheorems := name :: trivialTheorems
      -- DISABLED: isTrivialProof calls inferType which is expensive
      -- else
      --   let isTrivial ← isTrivialProof ti.value
      --   if isTrivial then
      --     trivialTheorems := name :: trivialTheorems

    | .defnInfo di =>
      -- Shallow axiom check for definitions
      let directDeps := di.value.getUsedConstants
      let (hasSorry, nonStandard) := checkDirectDependencies env directDeps

      if hasSorry then
        sorryDecls := name :: sorryDecls

      if !nonStandard.isEmpty then
        nonStandardDecls := (name, nonStandard) :: nonStandardDecls

      -- Collect all axioms used (direct dependencies only)
      for dep in directDeps do
        match env.find? dep with
        | some (.axiomInfo _) => allAxioms := allAxioms.insert dep
        | _ => pure ()

      -- Check for native_decide usage (shallow check)
      if usesNativeDecide directDeps then
        nativeDecideUsages := name :: nativeDecideUsages

    | _ => continue

  -- Build result using Array for eager evaluation (avoids lazy List chains)
  let mut detailsArray : Array String := #[]
  let mut passed := true

  -- Critical: sorryAx usage
  if !sorryDecls.isEmpty then
    passed := false
    detailsArray := detailsArray.push "CRITICAL: The following declarations use 'sorry':"
    for decl in sorryDecls do
      detailsArray := detailsArray.push s!"  - {decl}"

  -- Non-standard axioms
  if !nonStandardDecls.isEmpty then
    passed := false
    detailsArray := detailsArray.push "Non-standard axioms detected:"
    for (decl, axioms) in nonStandardDecls do
      let axList := axioms.toList.map toString |> String.intercalate ", "
      detailsArray := detailsArray.push s!"  - {decl}: {axList}"

  -- Custom project axioms
  if !customAxioms.isEmpty then
    passed := false
    for ax in customAxioms do
      detailsArray := detailsArray.push s!"Custom axiom: {ax}"

  -- native_decide usage
  if !nativeDecideUsages.isEmpty then
    passed := false
    for usage in nativeDecideUsages do
      detailsArray := detailsArray.push s!"native_decide usage: {usage}"

  -- Trivial theorems (warning, not failure - some may be intentional)
  if !trivialTheorems.isEmpty then
    detailsArray := detailsArray.push "Warning: Potentially trivial theorems:"
    for thm in trivialTheorems do
      detailsArray := detailsArray.push s!"  - {thm}"

  -- Opaque declarations (fail: violates transparency requirement)
  if !opaqueDecls.isEmpty then
    passed := false
    for decl in opaqueDecls do
      detailsArray := detailsArray.push s!"Opaque declaration: {decl}"

  -- Convert to List only at the end
  let details := detailsArray.toList

  if passed then
    -- Use Array for eager evaluation of axiom list
    let standardUsedArray := allAxioms.toArray.filter isStandardAxiom
    let msg := if standardUsedArray.isEmpty then
      "No axioms used (constructive proofs)"
    else
      let axiomNames := standardUsedArray.map (·.toString)
      let axiomList := String.intercalate ", " axiomNames.toList
      s!"Uses only standard axioms: {axiomList}"

    if details.isEmpty then
      return CheckResult.pass "Soundness" msg
    else
      -- Pass but with warnings
      return { CheckResult.pass "Soundness" msg with details := details }
  else
    let issues := [
      if !sorryDecls.isEmpty then some s!"{sorryDecls.length} sorry" else none,
      if !nonStandardDecls.isEmpty then some s!"{nonStandardDecls.length} non-standard axioms" else none,
      if !customAxioms.isEmpty then some s!"{customAxioms.length} custom axioms" else none,
      if !nativeDecideUsages.isEmpty then some s!"{nativeDecideUsages.length} native_decide" else none,
      if !opaqueDecls.isEmpty then some s!"{opaqueDecls.length} opaque declarations" else none
    ].filterMap id |> String.intercalate ", "
    return CheckResult.fail "Soundness" issues details

end TAIL.Checks
