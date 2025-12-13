# KM_Inspect - Kim Morrison Standard Verification Tool

A modular tool for verifying Lean 4 projects comply with the **Kim Morrison Standard** for AI-assisted formal mathematics.

## Purpose

When AI generates formal proofs, how can humans efficiently verify they're legitimate? The Kim Morrison Standard solves this by requiring:

1. **MainTheorem.lean** - Contains only `StatementOfTheorem : Prop`, imports **only Mathlib**
2. **ProofOfMainTheorem.lean** - Contains only `mainTheorem : StatementOfTheorem`, uses module system for private imports

This lets reviewers verify correctness by inspecting **only MainTheorem.lean** - everything else is machine-verified.

## Usage

```bash
# Run from project root (auto-detects project prefix from lakefile.lean)
lake exe kmverify

# Run with explicit project path
lake exe kmverify /path/to/project

# JSON output for CI
lake exe kmverify --json

# Write output to file
lake exe kmverify -o report.txt
```

No configuration file needed. All names are hardcoded per the Kim Morrison Standard:
- `MainTheorem.lean`, `ProofOfMainTheorem.lean`
- `StatementOfTheorem`, `mainTheorem`

Project prefix is auto-detected from `lakefile.lean`.

## Trust Tiers

### MainTheorem.lean
- **Imports**: Mathlib/Init/Lean/Batteries **only** (NO project imports)
- **Declarations**: Only `def StatementOfTheorem : Prop := ...`
- **Trust level**: Zero trust, requires full human review
- **Module system**: NOT used (standard file)

### ProofOfMainTheorem.lean
- **Imports**:
  - `public import Mathlib...` (re-exported to importers)
  - `import Project...` (private, not re-exported)
- **Declarations**: Exactly one theorem proving the statement in `public section`
- **Trust level**: Machine-verified via lean4checker
- **Module system**: REQUIRED (`module` keyword at start, `public section` for theorem)

## Verification Checks

| Check | Description |
|-------|-------------|
| Structure | `StatementOfTheorem : Prop` and `mainTheorem : StatementOfTheorem` exist; MainTheorem.lean imports only Mathlib |
| Soundness | Only standard axioms (propext, Quot.sound, Classical.choice, funext); no sorry; no native_decide; no custom axioms/opaques; trivial theorem warnings |
| ProofMinimality | ProofOfMainTheorem.lean contains exactly one theorem |
| MainTheoremPurity | MainTheorem.lean contains no theorems (only defs) |
| Module Visibility | Only `StatementOfTheorem` and `mainTheorem` are exported (requires module system) |
| Lean4Checker | Kernel verification via [lean4checker](https://github.com/leanprover/lean4checker) |

All checks use **environment introspection** rather than text parsing.

## Output

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

## File Structure

```
KM_Inspect/
  Main.lean              # CLI entry point, orchestration
  Types.lean             # CheckResult, TrustLevel, VerificationReport
  Config.lean            # Lakefile parsing, auto-detection
  FileUtils.lean         # Line counting utilities
  Environment.lean       # Lean environment introspection
  Report.lean            # Output formatting
  Checks/
    Structure.lean       # Required declarations + import verification
    Soundness.lean       # Axioms, sorry, native_decide, opaques, trivial theorems
    Imports.lean         # Module visibility (re-import test)
    ProofMinimality.lean # Exactly one theorem in proof file
    MainTheoremPurity.lean   # No theorems in MainTheorem
    Lean4Checker.lean    # Kernel verification via lean4checker
  README.md
```

## Module System Requirements

The Lean 4.20+ module system is essential for the Kim Morrison Standard:

```lean
-- ProofOfMainTheorem.lean
module                              -- Required: opt-in to module system

public import Mathlib               -- Required: Mathlib must be public
import MyProject.MainTheorem        -- Required: project imports must be private
import MyProject.Proofs.Helpers     -- Required: all helpers private

public section                      -- Required: theorem must be in public section
theorem mainTheorem : StatementOfTheorem := by
  ...
```

Enable in your `lakefile.lean`:
```lean
package MyProject where
  leanOptions := #[
    ⟨`experimental.module, true⟩
  ]
```

## Reference

- [Kim Morrison Standard discussion](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568)
- [Lean 4.20.0 Module System](https://lean-lang.org/doc/reference/latest/releases/v4.20.0/)
- [lean4checker](https://github.com/leanprover/lean4checker) - Kernel verification

## License

Apache 2.0
