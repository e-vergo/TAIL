# TAIL

**T**emplate for **AI**-generated **L**ean

A verification tool for Lean 4 projects that aims to reduce the review burden for AI generated mathematical proofs

## The TAIL Standard

[TAIL proposed](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs/near/556956052) a strict solution:

> Projects "don't count" unless:
> - They contain a file `MainTheorem.lean`, which has **no imports outside of Mathlib**, and contains the main result as `def StatementOfTheorem : Prop := ...`
> - They contain a file `ProofOfMainTheorem.lean` containing **nothing besides** `theorem mainTheorem : StatementOfTheorem := ...`

TAIL supports two modes:

### Strict Mode (Original TAIL Standard)
- `MainTheorem.lean` contains only `ProjectName.StatementOfTheorem`
- No `Definitions/` folder allowed
- Run with `--strict` flag

### Default Mode (Extended Standard)
- `MainTheorem.lean` can import from a `Definitions/` folder
- `Definitions/` contains supporting types, structures, and notations
- Both `MainTheorem.lean` and `Definitions/` require human review

With the Lean 4.27+ module system, `ProofOfMainTheorem.lean` uses **private imports** for internal proof machinery, ensuring that `import ProofOfMainTheorem` exposes only:
- The Mathlib re-exports
- `ProjectName.StatementOfTheorem` and `ProjectName.mainTheorem`

**Result:** A human reviewer needs only to read `MainTheorem.lean` (and `Definitions/` in default mode) to understand what is being proven.

## How It Works

### Required Structure

All names are hardcoded per the TAIL Standard:
- `MainTheorem.lean` - statement file
- `ProofOfMainTheorem.lean` - proof file
- `Definitions/` - supporting types (default mode only)
- `Proofs/` - helper lemmas (optional)
- `ProjectName.StatementOfTheorem` - the proposition being proven
- `ProjectName.mainTheorem` - the theorem proving it

The project prefix is auto-detected from your `lakefile.lean`.

#### Strict Mode Structure
```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
```

#### Default Mode Structure
```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── Definitions/                [HUMAN REVIEW]
│   └── *.lean
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
```

```lean
-- MainTheorem.lean (HUMAN REVIEW REQUIRED)
import Mathlib.Data.Complex.Basic  -- Mathlib only in strict mode
import MyProject.Definitions.Types -- Allowed in default mode

namespace MyProject

def StatementOfTheorem : Prop :=
  forall n : Nat, SomeInterestingProperty n

end MyProject
```

```lean
-- ProofOfMainTheorem.lean (MACHINE VERIFIED)
module                              -- Enable module system (Lean < 4.27)

public import Mathlib               -- Re-exported to importers
import MyProject.MainTheorem        -- Private (not re-exported)
import MyProject.Definitions        -- Private (not re-exported)
import MyProject.Proofs.Helpers     -- Private (not re-exported)

namespace MyProject

public section
theorem mainTheorem : StatementOfTheorem := by
  -- proof using private imports

end MyProject
```

### Verification Checks

| Check | Description |
|-------|-------------|
| Structure | `ProjectName.StatementOfTheorem : Prop` and `ProjectName.mainTheorem` exist; imports validated per mode |
| Soundness | Only standard axioms (propext, Quot.sound, Classical.choice, funext); no sorry; no native_decide; no custom axioms/opaques |
| ProofMinimality | ProofOfMainTheorem.lean contains exactly one theorem |
| StatementPurity | MainTheorem.lean contains no theorems; extra defs warn in default mode, error in strict mode |
| DefinitionsPurity | Definitions/ contains only defs/structures (no theorems); only imports Mathlib or other Definitions/ files |
| Module Visibility | Only `StatementOfTheorem` and `mainTheorem` are exported (requires module system) |
| Lean4Checker | Kernel verification via [lean4checker](https://github.com/leanprover/lean4checker) |

All checks use **environment introspection** rather than text parsing for maximum reliability.

## Installation

```bash
# Clone the repository
git clone https://github.com/e-vergo/KM_Inspection.git
cd KM_Inspection

# Build
lake exe cache get  # Download cached Mathlib (recommended)
lake build
```

## Usage

### Verifying a Project

```bash
# Run from the target project's root directory (default mode)
lake exe tailverify

# Strict mode (original TAIL Standard - no Definitions/ allowed)
lake exe tailverify --strict

# Or specify the project path
lake exe tailverify /path/to/project

# JSON output for CI integration
lake exe tailverify --json

# Write output to file
lake exe tailverify --output report.txt
```

### Creating a New Project

```bash
# Generate a TAIL Standard project structure
lake exe tailscaffold MyTheorem
cd MyTheorem
lake update
lake exe cache get
```

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All checks passed (VERIFIED) |
| 1 | One or more checks failed |
| 2 | Configuration error (missing lakefile, files, etc.) |
| 3 | Build error (project not compiled) |

### Example Output

#### Strict Mode
```
================================================================================
KIM MORRISON STANDARD COMPLIANCE REPORT
Project: MyProject
================================================================================

TRUST TIER SUMMARY (STRICT KIM MORRISON STANDARD)
--------------------------------------------------------------------------------
  [HUMAN REVIEW]
    MainTheorem.lean                            27 lines
  [MACHINE VERIFIED]
    ProofOfMainTheorem.lean                     60 lines
--------------------------------------------------------------------------------
  REVIEW BURDEN: 27 lines (MainTheorem.lean only)
  TOTAL: 87 lines (31% requires review)

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [PASS] Soundness
  [PASS] Proof Minimality
  [PASS] Statement Purity
  [PASS] Definitions Purity
  [PASS] Module Visibility
  [PASS] Lean4Checker

================================================================================
RESULT: PROJECT MEETS TEMPLATE EXPECTATIONS
================================================================================
```

#### Default Mode (with Definitions/)
```
================================================================================
KIM MORRISON STANDARD COMPLIANCE REPORT
Project: MyProject
================================================================================

TRUST TIER SUMMARY (EXTENDED KIM MORRISON STANDARD)
--------------------------------------------------------------------------------
  [HUMAN REVIEW]
    MainTheorem.lean                            27 lines
    Definitions/ (3 files)                      85 lines
  [MACHINE VERIFIED]
    ProofOfMainTheorem.lean                     60 lines
    Proofs/ (2 files)                           120 lines
--------------------------------------------------------------------------------
  REVIEW BURDEN: 112 lines (MainTheorem.lean + Definitions/)
  TOTAL: 292 lines (38% requires review)
```

## Integrating Into Your Project

1. Add TAIL as a dependency in your `lakefile.lean`:
   ```lean
   require TAIL from git
     "https://github.com/e-vergo/KM_Inspection"

   require lean4checker from git
     "https://github.com/leanprover/lean4checker"

   package MyProject where
     -- Note: experimental.module is no longer required as of Lean 4.27+
   ```

2. Organize your code following the standard:
   - `{ProjectPrefix}/MainTheorem.lean` with `ProjectName.StatementOfTheorem`
   - `{ProjectPrefix}/ProofOfMainTheorem.lean` with `ProjectName.mainTheorem`
   - `{ProjectPrefix}/Definitions/` for supporting types (default mode)
   - `{ProjectPrefix}/Proofs/` for helper lemmas (optional)

3. Run `lake exe tailverify` (or `lake exe tailverify --strict` for strict mode)

No configuration file needed - project prefix is auto-detected from `lakefile.lean`.

## Reference

- [TAIL's original proposal](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568)
- [Lean 4.20.0 Module System](https://lean-lang.org/doc/reference/latest/releases/v4.20.0/)
- [lean4checker](https://github.com/leanprover/lean4checker) - Kernel verification
- [Lean 4](https://leanprover.github.io/)
- [Mathlib](https://leanprover-community.github.io/)

## License

Apache 2.0