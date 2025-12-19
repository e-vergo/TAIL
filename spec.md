# TAIL Update Plan: Strict vs Default Mode Specification

## Overview

This plan defines the two verification modes for TAIL, specifying exactly what declarations and imports are allowed in each file/folder.

---

## File Structure

### Strict Mode (Original Kim Morrison Standard)

```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
    └── *.lean
```

### Default Mode (Extended Standard)

```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── Definitions/                [HUMAN REVIEW]
│   └── *.lean
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
    └── *.lean
```

---

## Namespace Requirement (Both Modes)

Per Kim's suggestion, to prevent collisions in transitive dependencies:

| Declaration | Required Namespace |
|-------------|-------------------|
| `StatementOfTheorem` | `ProjectName.StatementOfTheorem` |
| `mainTheorem` | `ProjectName.mainTheorem` |

The project name is auto-detected from `lakefile.lean`.

---

## Strict Mode: Allowed Declarations & Imports

### MainTheorem.lean

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | Mathlib, Init, Std, Lean, Qq, Aesop, ProofWidgets, Batteries | Any project imports |
| **Declarations** | `def StatementOfTheorem : Prop` | Any other `def` |
| | | `abbrev`, `notation`, `instance` |
| | | Any `theorem` |
| | | Any `axiom` |
| | | Any `opaque` |

**Note:** Strict mode enforces the original Kim Morrison proposal: MainTheorem.lean contains *only* `StatementOfTheorem`.

### ProofOfMainTheorem.lean

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | `public import Mathlib.*` (re-exported) | |
| | `import ProjectName.MainTheorem` (private) | |
| | `import ProjectName.Proofs.*` (private) | |
| **Declarations** | `theorem mainTheorem : StatementOfTheorem` | Additional public theorems |
| | Private helper lemmas (via `private` or module system) | Public definitions |
| **Module System** | `module` keyword (Lean < 4.27) or default behavior (Lean 4.27+) | |

### Proofs/ (optional)

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | Mathlib, project files | |
| **Declarations** | Any `def`, `theorem`, `lemma` | `axiom` |
| | | `opaque` |
| | | `sorry` |

**Strict Mode Violations → Errors**

---

## Default Mode: Allowed Declarations & Imports

### MainTheorem.lean

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | Mathlib, Init, Std, Lean, Qq, Aesop, ProofWidgets, Batteries | Project imports outside `Definitions/` |
| | `import ProjectName.Definitions.*` | |
| **Declarations** | `def StatementOfTheorem : Prop` | Any `theorem` |
| | | Any `axiom` |
| | | Any `opaque` |
| | | `abbrev`, `notation`, `instance` |

**Note:** Additional `def`s in MainTheorem.lean trigger a **warning** (not error), recommending they be moved to `Definitions/`. For `abbrev`, `notation`, and `instance`, use `Definitions/` instead.

### Definitions/ (new)

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | Mathlib, Init, Std, Lean, Qq, Aesop, ProofWidgets, Batteries | Project imports outside `Definitions/` |
| | Other files within `Definitions/` | Imports from `Proofs/` |
| **Declarations** | `def` | Any `theorem` |
| | `abbrev` | Any `axiom` |
| | `notation` | Any `opaque` |
| | `structure` | `sorry` |
| | `inductive` | |
| | `class` | |
| | `instance` | |

**Purpose:** Contains all definitions that `StatementOfTheorem` depends on. Reviewer must understand these to trust the theorem statement. This is the proper place for `abbrev`, `notation`, and `instance` declarations needed for the theorem statement.

### ProofOfMainTheorem.lean

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | `public import Mathlib.*` (re-exported) | |
| | `import ProjectName.MainTheorem` (private, not re-exported) | |
| | `import ProjectName.Definitions.*` (private, not re-exported) | |
| | `import ProjectName.Proofs.*` (private, not re-exported) | |
| **Declarations** | `theorem mainTheorem : StatementOfTheorem` | Additional public theorems |
| | Private helper lemmas | Public definitions |

**Note:** All project imports are private. Only Mathlib is re-exported. Definitions/ contents are NOT visible to downstream importers.

### Proofs/ (optional)

| Category | Allowed | Disallowed |
|----------|---------|------------|
| **Imports** | Mathlib, `Definitions/`, other `Proofs/` files | |
| **Declarations** | Any `def`, `theorem`, `lemma` | `axiom` |
| | | `opaque` |
| | | `sorry` |

---

## Soundness Rules (Both Modes)

These apply universally across all files:

| Rule | Description |
|------|-------------|
| **Standard Axioms Only** | `propext`, `Quot.sound`, `Classical.choice`, `funext` |
| **No sorry** | `sorryAx` forbidden anywhere in proof tree |
| **No native_decide** | `Lean.ofReduceBool`, `Lean.ofReduceNat` forbidden |
| **No custom axioms** | Project-defined `axiom` declarations forbidden |
| **No opaque** | All definitions must be transparent |

---

## Module Visibility (Both Modes)

When importing `ProofOfMainTheorem`, only these project declarations should be visible:

| Declaration | Source |
|-------------|--------|
| `ProjectName.StatementOfTheorem` | MainTheorem.lean |
| `ProjectName.mainTheorem` | ProofOfMainTheorem.lean |

Everything else (Definitions/, Proofs/, helper lemmas) must be private via the module system.

---

## Verification Report: Review Burden

### Strict Mode

```
REVIEW BURDEN: X lines (MainTheorem.lean only)
```

### Default Mode

```
REVIEW BURDEN: X lines (MainTheorem.lean + Definitions/)
  - MainTheorem.lean: Y lines
  - Definitions/: Z lines (N files)
```

---

## Check Naming Updates

| Current Name | New Name |
|--------------|----------|
| MainTheoremPurity | StatementPurity |
| (new) | DefinitionsPurity |