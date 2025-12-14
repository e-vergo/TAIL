/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import TAIL.Types
import TAIL.Config

/-!
# Soundness Check

Comprehensive soundness verification for Kim Morrison Standard compliance.

## Checks Performed

1. **Axiom Safety**: Verify only standard axioms are used (propext, Quot.sound, Classical.choice, funext)
2. **No Sorry**: Ensure no incomplete proofs (sorryAx usage)
3. **No Custom Axioms**: No project-defined axioms
4. **No native_decide**: Avoid non-kernel-verified decision procedures
5. **No Opaque Declarations**: Ensure all definitions are transparent
6. **No Trivial Theorems**: Detect True, trivial, and other placeholder proofs

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

/-! ## Deep Axiom Traversal -/

/-- Get all axioms a declaration depends on (recursive traversal) -/
def getAxioms (declName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some _ := env.find? declName
    | throwError "Declaration {declName} not found"

  let mut axioms : Array Name := #[]
  let mut visited : Std.HashSet Name := {}
  let mut toVisit : Array Name := #[declName]

  while h : toVisit.size > 0 do
    let curr := toVisit[toVisit.size - 1]'(by omega)
    toVisit := toVisit.pop

    if visited.contains curr then
      continue
    visited := visited.insert curr

    let some currInfo := env.find? curr
      | continue

    match currInfo with
    | .axiomInfo _ =>
      axioms := axioms.push curr
    | .defnInfo val =>
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | .thmInfo val =>
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | _ => continue

  return axioms

/-! ## native_decide Detection -/

/-- Check if an expression contains a reference to native_decide (Lean.ofReduceBool) -/
partial def containsNativeDecide (e : Expr) : Bool :=
  match e with
  | .const name _ => name == ``Lean.ofReduceBool || name == ``Lean.ofReduceNat
  | .app f a => containsNativeDecide f || containsNativeDecide a
  | .lam _ t b _ => containsNativeDecide t || containsNativeDecide b
  | .forallE _ t b _ => containsNativeDecide t || containsNativeDecide b
  | .letE _ t v b _ => containsNativeDecide t || containsNativeDecide v || containsNativeDecide b
  | .mdata _ e => containsNativeDecide e
  | .proj _ _ e => containsNativeDecide e
  | _ => false

/-! ## Trivial Theorem Detection -/

/-- Trivial proof terms that indicate placeholder or meaningless theorems -/
def trivialProofConstants : List Name :=
  [`True.intro, `trivial, `rfl]

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
def checkSoundness (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let projectPrefix := resolved.projectPrefix

  let mut allAxioms : Std.HashSet Name := {}
  let mut sorryDecls : List Name := []
  let mut nonStandardDecls : List (Name × Array Name) := []
  let mut customAxioms : List Name := []
  let mut opaqueDecls : List Name := []
  let mut nativeDecideUsages : List Name := []
  let mut trivialTheorems : List Name := []

  -- Check ALL project declarations
  for (name, info) in env.constants.toList do
    let nameStr := name.toString
    if !nameStr.startsWith projectPrefix then
      continue

    match info with
    | .axiomInfo _ =>
      -- Custom project axioms are not allowed
      if !isStandardAxiom name && name != ``sorryAx then
        customAxioms := name :: customAxioms

    | .opaqueInfo _ =>
      opaqueDecls := name :: opaqueDecls

    | .thmInfo ti =>
      -- Deep axiom check
      try
        let axioms ← getAxioms name

        -- Track sorryAx usage
        if axioms.contains ``sorryAx then
          sorryDecls := name :: sorryDecls

        -- Track non-standard axioms (excluding sorryAx which is tracked separately)
        let nonStandard := axioms.filter (fun ax => !isStandardAxiom ax && ax != ``sorryAx)
        if !nonStandard.isEmpty then
          nonStandardDecls := (name, nonStandard) :: nonStandardDecls

        -- Collect all axioms used
        for ax in axioms do
          allAxioms := allAxioms.insert ax
      catch _ => pure ()

      -- Check for native_decide usage
      if containsNativeDecide ti.value then
        nativeDecideUsages := name :: nativeDecideUsages

      -- Check for trivial theorems (type is True, proof is trivial)
      if hasTrivialType ti.type then
        trivialTheorems := name :: trivialTheorems
      else
        -- Also check if proof term is trivial
        let isTrivial ← isTrivialProof ti.value
        if isTrivial then
          trivialTheorems := name :: trivialTheorems

    | .defnInfo di =>
      -- Deep axiom check for definitions
      try
        let axioms ← getAxioms name

        if axioms.contains ``sorryAx then
          sorryDecls := name :: sorryDecls

        let nonStandard := axioms.filter (fun ax => !isStandardAxiom ax && ax != ``sorryAx)
        if !nonStandard.isEmpty then
          nonStandardDecls := (name, nonStandard) :: nonStandardDecls

        for ax in axioms do
          allAxioms := allAxioms.insert ax
      catch _ => pure ()

      -- Check for native_decide usage
      if containsNativeDecide di.value then
        nativeDecideUsages := name :: nativeDecideUsages

    | _ => continue

  -- Build result
  let mut details : List String := []
  let mut passed := true

  -- Critical: sorryAx usage
  if !sorryDecls.isEmpty then
    passed := false
    details := details ++ ["CRITICAL: The following declarations use 'sorry':"]
    details := details ++ sorryDecls.map (s!"  - {·}")

  -- Non-standard axioms from deep traversal
  if !nonStandardDecls.isEmpty then
    passed := false
    details := details ++ ["Non-standard axioms detected:"]
    for (decl, axioms) in nonStandardDecls do
      let axList := axioms.toList.map toString |> String.intercalate ", "
      details := details ++ [s!"  - {decl}: {axList}"]

  -- Custom project axioms
  if !customAxioms.isEmpty then
    passed := false
    details := details ++ customAxioms.map (s!"Custom axiom: {·}")

  -- native_decide usage
  if !nativeDecideUsages.isEmpty then
    passed := false
    details := details ++ nativeDecideUsages.map (s!"native_decide usage: {·}")

  -- Trivial theorems (warning, not failure - some may be intentional)
  if !trivialTheorems.isEmpty then
    details := details ++ ["Warning: Potentially trivial theorems:"]
    details := details ++ trivialTheorems.map (s!"  - {·}")

  -- Opaque declarations (warning, not failure)
  if !opaqueDecls.isEmpty then
    details := details ++ opaqueDecls.map (s!"Opaque declaration: {·}")

  if passed then
    let standardUsed := allAxioms.toList.filter isStandardAxiom
    let msg := if standardUsed.isEmpty then
      "No axioms used (constructive proofs)"
    else
      let axiomList := standardUsed.map toString |> String.intercalate ", "
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
      if !nativeDecideUsages.isEmpty then some s!"{nativeDecideUsages.length} native_decide" else none
    ].filterMap id |> String.intercalate ", "
    return CheckResult.fail "Soundness" issues details

end TAIL.Checks
