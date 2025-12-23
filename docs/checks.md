# Verification Checks

TAIL performs 10 verification checks organized into four categories.

## Structure

| Check | Description |
|-------|-------------|
| **Structure** | `ProjectName.StatementOfTheorem : Prop` and `ProjectName.mainTheorem` exist |

The Structure check verifies that the required declarations exist and have correct types.

## Soundness

| Check | Description |
|-------|-------------|
| **Soundness** | No uses of `sorry`, `native_decide`, trivial `True`, or `partial`/`unsafe` defs |
| **Axioms in Source** | No `axiom` declarations |
| **Opaques in Source** | No `opaque` declarations |
| **Unsafe Attributes** | No `@[implemented_by]` or `@[extern]`|

### Soundness Details

The main Soundness check detects:
- `sorry` - Incomplete proofs
- `native_decide` - Unverified computational decisions
- Trivial `True` proofs - Proving something meaningless
- `partial def` - Non-termination risk
- `unsafe def` - Bypasses type checker

### Source-Based Checks

Axioms, Opaques, and Unsafe Attributes are detected by scanning source files directly. This is necessary because Lean's module system stores `public section` declarations as axioms in `.olean` files.

## Content Rules

| Check | Description |
|-------|-------------|
| **ProofOfMainTheorem Isolation** | Exposes exactly one public theorem |
| **MainTheorem Isolation** | Contains no theorems (only definitions) |
| **Proofs Content** | Contains only lemmas and Prop-valued definitions |
| **Definitions Content** | Contains defs, structures, and theorems |

### ProofOfMainTheorem Isolation

`ProofOfMainTheorem.lean` must expose exactly one theorem: `mainTheorem`. Additional theorems would leak proof machinery into the public API.

### MainTheorem Isolation

`MainTheorem.lean` should contain only the `StatementOfTheorem` definition. Theorems are not allowed because they would require proof code in the human-review tier.

### Proofs Content

Files in `Proofs/` may only contain:
- Lemmas (theorem declarations)
- Prop-valued definitions

Structures, inductives, and non-Prop defs belong in `Definitions/`.

### Definitions Content

Files in `Definitions/` may contain:
- Definitions (`def`)
- Structures and inductives
- Theorems (for dependent types)
- Notations and macros (generates a warning)

## Import Discipline

| Check | Description |
|-------|-------------|
| **Import Discipline** | MainTheorem.lean only imports Mathlib (strict) or Mathlib + Definitions/ (default) |

This ensures the theorem statement's semantics are clear:
- **Strict mode**: Only Mathlib imports allowed
- **Default mode**: Mathlib + project's own `Definitions/` imports allowed

## Verification Architecture

TAIL uses a hybrid approach:

### Olean-Based Checks
- Structure, Soundness, Isolation, Content, Import checks
- Reads compiled `.olean` files directly
- Fast verification (~1 second) without importing the project

### Source-Based Checks
- Axiom, Opaque, Unsafe Attribute detection
- Scans `.lean` source files with regex patterns
- Necessary because olean files don't distinguish user axioms from module system axioms

## Warnings

In addition to pass/fail checks, TAIL generates warnings for:
- Custom `notation` in Definitions/
- `macro` definitions in Definitions/

These don't fail verification but require extra review since they can affect MainTheorem.lean semantics.
