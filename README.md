# TAIL

**T**emplate for **AI**-generated **L**ean

A verification tool for Lean 4 projects that reduces the review burden for AI-generated mathematical proofs.

## The TAIL Standard

[TAIL proposed](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/near/556956052) a strict solution:

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

## Quick Start

### Verifying an Existing Project

```bash
# Clone TAIL
git clone https://github.com/e-vergo/TAIL.git
cd TAIL

# Build
lake exe cache get  # Download cached Mathlib
lake build

# Verify a project (default mode)
lake exe tailverify /path/to/your/project

# Verify in strict mode
lake exe tailverify --strict /path/to/your/project
```

### Creating a New TAIL-Compliant Project

```bash
# Generate a new project structure
lake exe tailscaffold MyTheorem
cd MyTheorem
lake update
lake exe cache get
```

## Project Structure

All names are hardcoded per the TAIL Standard:
- `MainTheorem.lean` - statement file
- `ProofOfMainTheorem.lean` - proof file
- `Definitions/` - supporting types (default mode only)
- `Proofs/` - helper lemmas (optional)
- `ProjectName.StatementOfTheorem` - the proposition being proven
- `ProjectName.mainTheorem` - the theorem proving it

The project prefix is auto-detected from your `lakefile.lean`.

### Strict Mode Structure
```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
```

### Default Mode Structure
```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── Definitions/                [HUMAN REVIEW]
│   └── *.lean
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
```

### Example Files

```lean
-- MainTheorem.lean (HUMAN REVIEW REQUIRED)
module

public import Mathlib.Data.Complex.Basic  -- Mathlib only in strict mode
public import MyProject.Definitions.Types -- Allowed in default mode

namespace MyProject

@[expose] public section

def StatementOfTheorem : Prop :=
  forall n : Nat, SomeInterestingProperty n

end

end MyProject
```

```lean
-- ProofOfMainTheorem.lean (MACHINE VERIFIED)
module

public import Mathlib               -- Re-exported to importers
public import MyProject.MainTheorem -- Re-exported (contains StatementOfTheorem)
import MyProject.Proofs.Helpers     -- Private (not re-exported)

namespace MyProject

@[expose] public section

theorem mainTheorem : StatementOfTheorem := by
  -- proof using private imports

end

end MyProject
```

## Verification Checks

| Check | Description |
|-------|-------------|
| Structure | `ProjectName.StatementOfTheorem : Prop` and `ProjectName.mainTheorem` exist |
| Soundness | No sorry; no native_decide; no trivial `True` declarations (via olean) |
| Axioms in Source | No `axiom` declarations in source files (via source scanning) |
| Proof Minimality | ProofOfMainTheorem.lean contains exactly one public theorem |
| MainTheorem Isolation | MainTheorem.lean contains no theorems; extra defs warn in default mode, error in strict mode |
| Import Discipline | MainTheorem.lean only imports Mathlib (strict) or Mathlib + Definitions/ (default) |
| Proofs Purity | Proofs/ contains only lemmas and Prop-valued definitions (no structures, no data defs) |
| Definitions Purity | Definitions/ contains only defs/structures (no theorems, no sorry) |

### Verification Architecture

TAIL uses a hybrid approach for fast, reliable verification:

- **Olean-based checks**: Structure, Soundness, Proof Minimality, Isolation, Imports, Purity checks read compiled `.olean` files directly for fast verification (~1 second) without importing the project.

- **Source-based checks**: Axiom detection scans `.lean` source files for `axiom` and `private axiom` declarations. This is necessary because Lean's module system stores `public section` theorems as axioms in olean files, making olean-based axiom detection unreliable.

## CLI Usage

```bash
# Default mode (allows Definitions/ folder)
lake exe tailverify [directory]

# Strict mode (original TAIL Standard)
lake exe tailverify --strict [directory]

# Additional options
lake exe tailverify --json              # JSON output for CI
lake exe tailverify --output report.txt # Write to file
lake exe tailverify --report            # Generate tail_compliance_report.txt
lake exe tailverify --prefix MyProject  # Override auto-detected prefix
lake exe tailverify --help              # Show all options
```

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All checks passed |
| 1 | One or more checks failed |
| 2 | Configuration error (missing lakefile, files, etc.) |
| 3 | Build error (project not compiled) |

## Example Output

### Passing Project (Default Mode)
```
================================================================================
TAIL STANDARD COMPLIANCE REPORT
Project: PassAll
Tool: TAIL v0.1
================================================================================

TRUST TIER SUMMARY (EXTENDED TAIL STANDARD)
--------------------------------------------------------------------------------
  [HUMAN REVIEW]
    MainTheorem.lean                            28 lines
    Definitions/ (1 files)                     30 lines
  [MACHINE VERIFIED]
    ProofOfMainTheorem.lean                     20 lines
    Proofs/ (1 files)                         32 lines
--------------------------------------------------------------------------------
  REVIEW BURDEN: 58 lines (MainTheorem.lean + Definitions/)
  TOTAL: 110 lines (52% requires review)

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [PASS] Soundness
  [PASS] Axioms in Source
  [PASS] Proof Minimality
  [PASS] MainTheorem Isolation
  [PASS] Import Discipline
  [PASS] Proofs Purity
  [PASS] Definitions Purity

================================================================================
RESULT: PROJECT MEETS TEMPLATE EXPECTATIONS

This project meets the TAIL Standard for AI-generated formal proofs.
A human reviewer only needs to verify MainTheorem.lean to trust the result.
================================================================================
```

### Failing Project
```
================================================================================
TAIL STANDARD COMPLIANCE REPORT
Project: FailAll
Tool: TAIL v0.1
================================================================================

...

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [FAIL] Soundness
           - FailAll.ProofOfMainTheorem: FailAll.mainTheorem (sorry)
           - FailAll.MainTheorem: FailAll.badTheorem (trivial True)
  [FAIL] Axioms in Source
           - FailAll/Proofs/BadHelper.lean:24: axiom bad : 1 + 3 = 2
  [FAIL] Proof Minimality
         Multiple theorems/axioms found (3):
           - theorem FailAll.extraTheorem
           - theorem FailAll.anotherExtraTheorem
           - theorem FailAll.mainTheorem
  [FAIL] MainTheorem Isolation
         ERROR: theorem FailAll.badTheorem (theorems not allowed in MainTheorem.lean)
  [FAIL] Import Discipline
         MainTheorem.lean import violations:
           - FailAll.Proofs.BadHelper (project import not allowed)
  ...

================================================================================
RESULT: PROJECT FAILS TO MEET TEMPLATE EXPECTATIONS

Please fix the issues above before requesting review.
================================================================================
```

## Integrating Into Your Project

### Option 1: Run from TAIL Repository

```bash
# Clone and build TAIL once
git clone https://github.com/e-vergo/TAIL.git
cd TAIL && lake build

# Verify any project
lake exe tailverify /path/to/your/project
```

### Option 2: Add as Dependency

Add TAIL as a dev dependency in your `lakefile.lean`:

```lean
require TAIL from git
  "https://github.com/e-vergo/TAIL.git"

package MyProject where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib MyProject where
```

Then run:
```bash
lake build
lake exe tailverify
```

## Test Fixtures

The repository includes test fixtures demonstrating correct and incorrect project structures:

| Fixture | Mode | Description |
|---------|------|-------------|
| `TestFixtures/PassAll` | default | Passes all checks (with Definitions/) |
| `TestFixtures/PassAllStrict` | strict | Passes all checks (no Definitions/) |
| `TestFixtures/FailAll` | default | Fails multiple checks (for testing) |
| `TestFixtures/FailAllStrict` | strict | Fails strict-mode checks (for testing) |

Run the test fixtures:
```bash
lake exe tailverify TestFixtures/PassAll           # Should pass
lake exe tailverify --strict TestFixtures/PassAllStrict  # Should pass
lake exe tailverify TestFixtures/FailAll           # Should fail
lake exe tailverify --strict TestFixtures/FailAllStrict  # Should fail
```

## Reference

- [TAIL's original proposal](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568)
- [Lean 4.20.0 Module System](https://lean-lang.org/doc/reference/latest/releases/v4.20.0/)
- [lean4checker](https://github.com/leanprover/lean4checker) - Kernel verification
- [Lean 4](https://leanprover.github.io/)
- [Mathlib](https://leanprover-community.github.io/)

## License

Apache 2.0
