# Verification Checks

TAIL performs 3 core verification checks plus an optional SafeVerify check for kernel-level verification.

## Trust Tier Model

TAIL enforces a two-tier trust model:

| Tier | Files | Constraint |
|------|-------|------------|
| **Human Review** | MainTheorem.lean, Definitions/ | No restrictions - reviewer checks all of this |
| **Machine Verified** | ProofOfMainTheorem.lean, Proofs/ | Only Prop-valued declarations allowed |

The key insight: non-Prop declarations (structures, inductives, data-returning defs) **must** be in the human-review tier. This ensures that anything in the machine-verified tier can be trusted without human review.

## Core Checks

### 1. Structure

| Check | Description |
|-------|-------------|
| **Structure** | Required declarations exist with correct types |

Verifies:
- `ProjectName.StatementOfTheorem` exists as a `def` in MainTheorem.lean
- `ProjectName.mainTheorem` exists as a `theorem` in ProofOfMainTheorem.lean

### 2. Trust Tier

| Check | Description |
|-------|-------------|
| **Trust Tier** | Machine-verified tier contains only Prop-valued declarations |

The machine-verified tier (ProofOfMainTheorem.lean + Proofs/) may only contain:
- Theorems (inherently Prop-valued)
- Prop-valued definitions (e.g., `def myProp : Prop := ...`)

The following are **rejected** in the machine-verified tier:
- Structures and inductives (use Definitions/ instead)
- Data-returning definitions (e.g., `def compute : Nat := ...`)

This is the core enforcement mechanism: if you want to define data types or non-Prop defs, they must go in the human-review tier where a reviewer will examine them.

### 3. Import Discipline

| Check | Description |
|-------|-------------|
| **Import Discipline** | MainTheorem.lean only imports approved sources |

Controls what MainTheorem.lean can import:
- **Strict mode** (`--strict`): Only Mathlib imports allowed
- **Default mode**: Mathlib + project's Definitions/ imports allowed

This ensures the theorem statement's semantics are clear and verifiable.

## Verification Architecture

TAIL reads compiled `.olean` files directly for fast verification (~1 second) without importing the full project environment. This approach:

1. Extracts declaration metadata (names, types, kinds) from olean files
2. Uses type information to determine if declarations are Prop-valued
3. Analyzes import graphs to verify import discipline

## Warnings

In addition to pass/fail checks, TAIL generates warnings for semantic risks in Definitions/:

- Custom `notation` declarations
- `macro` definitions
- `syntax` declarations
- Coercion instances (`Coe`, `CoeFun`, etc.)

These don't fail verification but alert reviewers that MainTheorem.lean semantics could be affected.

Example warning:
```
WARNING: Project/Definitions/Types.lean contains custom notation (line 32) - verify MainTheorem.lean semantics
```

## Optional: SafeVerify Integration

| Check | Description |
|-------|-------------|
| **SafeVerify** | Kernel-level re-verification via SafeVerify subprocess |

SafeVerify provides more robust soundness verification by re-checking proofs through the Lean kernel at the term level. Enable with `--safeverify` flag:

```bash
lake exe tailverify --safeverify /path/to/project
```

### What SafeVerify Checks

SafeVerify performs kernel-level verification including:
- Re-verification of all declarations through the kernel
- Axiom usage restrictions (only standard axioms allowed)
- Detection of sorry, partial, unsafe at kernel level

### Requirements

SafeVerify must be installed separately. See [SafeVerify on GitHub](https://github.com/GasStationManager/SafeVerify) for installation instructions.

### When to Use

- **Development**: Use standard checks (`lake exe tailverify`) for fast feedback
- **Final verification**: Add `--safeverify` for robust kernel-level verification before sharing

## Design Philosophy

TAIL delegates soundness checking to SafeVerify and focuses on what it does best: **trust tier enforcement**. The core question TAIL answers is:

> "Are all non-Prop declarations in the human-review tier?"

If yes, then a human reviewer only needs to examine MainTheorem.lean (+ Definitions/ in default mode) to understand what's being claimed. The proof machinery in ProofOfMainTheorem.lean and Proofs/ can be trusted because it contains only propositions.
