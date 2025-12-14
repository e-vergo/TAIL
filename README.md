# KM_Inspect

A verification tool for Lean 4 projects that aims to reduce the review burden for AI generated mathematical proofs

## The Kim Morrison Standard

[Kim Morrison proposed](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs/near/556956052) a strict solution:

> Projects "don't count" unless:
> - They contain a file `MainTheorem.lean`, which has **no imports outside of Mathlib**, and contains the main result as `def StatementOfTheorem : Prop := ...`
> - They contain a file `ProofOfMainTheorem.lean` containing **nothing besides** `theorem mainTheorem : StatementOfTheorem := ...`

With the [Lean 4.20+ module system](https://lean-lang.org/doc/reference/latest/releases/v4.20.0/), Kim's vision is fully realized: `ProofOfMainTheorem.lean` can use **private imports** for internal proof machinery, ensuring that `import ProofOfMainTheorem` exposes only:
- The Mathlib re-exports
- `StatementOfTheorem` and `mainTheorem`

**Result:** A human reviewer needs only to read `MainTheorem.lean` to understand what is being proven.

## How It Works

### Required Structure

All names are hardcoded per the Kim Morrison Standard:
- `MainTheorem.lean` - statement file
- `ProofOfMainTheorem.lean` - proof file
- `StatementOfTheorem` - the proposition being proven
- `mainTheorem` - the theorem proving it

The project prefix is auto-detected from your `lakefile.lean`.

```lean
-- MainTheorem.lean (HUMAN REVIEW REQUIRED)
import Mathlib.Data.Complex.Basic  -- Mathlib only! No project imports allowed.

def StatementOfTheorem : Prop :=
  forall n : Nat, SomeInterestingProperty n
```

```lean
-- ProofOfMainTheorem.lean (MACHINE VERIFIED)
module                              -- Enable module system

public import Mathlib               -- Re-exported to importers
import MyProject.MainTheorem        -- Private (not re-exported)
import MyProject.Proofs.Helpers     -- Private (not re-exported)

public section
theorem mainTheorem : StatementOfTheorem := by
  -- proof using private imports
```

### Verification Checks

| Check | Description |
|-------|-------------|
| Structure | `StatementOfTheorem : Prop` and `mainTheorem : StatementOfTheorem` exist; MainTheorem.lean imports only Mathlib |
| Soundness | Only standard axioms (propext, Quot.sound, Classical.choice, funext); no sorry; no native_decide; no custom axioms/opaques |
| ProofMinimality | ProofOfMainTheorem.lean contains exactly one theorem |
| MainTheoremPurity | MainTheorem.lean contains no theorems (only defs) |
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
# Run from the target project's root directory
lake exe kmverify

# Or specify the project path
lake exe kmverify /path/to/project

# JSON output for CI integration
lake exe kmverify --json

# Write output to file
lake exe kmverify --output report.txt
```

### Creating a New Project

```bash
# Generate a Kim Morrison Standard project structure
lake exe kmscaffold MyTheorem
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

```
================================================================================
KIM MORRISON STANDARD VERIFICATION
Project: MyProject
================================================================================

TRUST TIER SUMMARY (STRICT KIM MORRISON STANDARD)
--------------------------------------------------------------------------------
  MainTheorem.lean                              27 lines  [HUMAN REVIEW]
  ProofOfMainTheorem.lean                       60 lines  [MACHINE VERIFIED]
--------------------------------------------------------------------------------
  REVIEW BURDEN: 27 lines (MainTheorem.lean only)
  TOTAL: 87 lines (31% requires review)

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [PASS] Soundness
  [PASS] Proof Minimality
  [PASS] MainTheorem Purity
  [PASS] Module Visibility
  [PASS] Lean4Checker

================================================================================
RESULT: PROJECT VERIFIED
================================================================================
```

## Integrating Into Your Project

1. Add KM_Inspect as a dependency in your `lakefile.lean`:
   ```lean
   require KM_Inspect from git
     "https://github.com/e-vergo/KM_Inspection"

   require lean4checker from git
     "https://github.com/leanprover/lean4checker"

   package MyProject where
     leanOptions := #[
       ⟨`experimental.module, true⟩  -- Enable module system
     ]
   ```

2. Organize your code following the strict standard:
   - `{ProjectPrefix}/MainTheorem.lean` with only Mathlib imports
   - `{ProjectPrefix}/ProofOfMainTheorem.lean` using module system

3. Run `lake exe kmverify`

No configuration file needed - project prefix is auto-detected from `lakefile.lean`.

## Reference

- [Kim Morrison's original proposal](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568)
- [Lean 4.20.0 Module System](https://lean-lang.org/doc/reference/latest/releases/v4.20.0/)
- [lean4checker](https://github.com/leanprover/lean4checker) - Kernel verification
- [Lean 4](https://leanprover.github.io/)
- [Mathlib](https://leanprover-community.github.io/)

## License

Apache 2.0