# The TAIL Standard

**T**emplate for **AI**-generated **L**ean

## Origin

The TAIL Standard addresses a fundamental challenge: how can humans trust AI-generated mathematical proofs? While Lean's type checker guarantees logical validity, a malicious or confused AI could prove something trivially true while appearing to prove something meaningful.

[TAIL was proposed](https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.20proofs/near/556956070) as a strict solution:

> Projects "don't count" unless:
> - They contain a file `MainTheorem.lean`, which has **no imports outside of Mathlib**, and contains the main result as `def StatementOfTheorem : Prop := ...`
> - They contain a file `ProofOfMainTheorem.lean` containing **nothing besides** `theorem mainTheorem : StatementOfTheorem := ...`

## Trust Tiers

TAIL divides project files into two trust levels:

### Human Review Required
- `MainTheorem.lean` - Contains `StatementOfTheorem : Prop`
- `Definitions/` (default mode only) - Supporting types and structures

These files define *what* is being proven. A human must read and understand them.

### Machine Verified
- `ProofOfMainTheorem.lean` - Contains `mainTheorem : StatementOfTheorem`
- `Proofs/` - Helper lemmas

These files prove *how* the theorem holds. Lean's type checker guarantees correctness.

## Verification Modes

### Strict Mode

The original TAIL Standard. MainTheorem.lean imports only from Mathlib.

```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED]
```

**Use strict mode when:** Your theorem statement uses only concepts already defined in Mathlib.

```bash
lake exe tailverify --strict
lake exe tailscaffold --strict MyProject
```

### Default Mode (Extended Standard)

Allows a `Definitions/` folder for custom types, structures, and notations that are needed in the theorem statement.

```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── Definitions/                [HUMAN REVIEW]
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED]
```

**Use default mode when:** Your theorem requires custom definitions that don't exist in Mathlib.

```bash
lake exe tailverify
lake exe tailscaffold MyProject
```

## Module System

TAIL leverages Lean 4.27+'s module system to enforce isolation:

```lean
-- ProofOfMainTheorem.lean
module

public import Mathlib.Tactic           -- Re-exported to importers
public import MyProject.MainTheorem    -- Re-exported (StatementOfTheorem visible)
import MyProject.Proofs.Helpers        -- Private (not re-exported)
```

When another project imports `MyProject.ProofOfMainTheorem`, they see:
- Mathlib exports
- `MyProject.StatementOfTheorem`
- `MyProject.mainTheorem`

They do **not** see the internal proof machinery in `Proofs/`.

## Why This Matters

Without TAIL, a reviewer must read every line of proof code to trust an AI-generated result. With TAIL:

1. **Reduced review burden**: Only `MainTheorem.lean` (+ `Definitions/`) requires human review
2. **Clear semantics**: The theorem statement is isolated from proof machinery
3. **Verified trust boundary**: TAIL tooling enforces the separation
