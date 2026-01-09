# CLI Reference

## tailverify

Verify a Lean project follows the TAIL Standard.

### Usage

```bash
lake exe tailverify [directory] [options]
```

### Options

| Option | Description |
|--------|-------------|
| `--strict` | Strict mode: no Definitions/ folder allowed |
| `--safeverify` | Run SafeVerify kernel verification (requires SafeVerify installed) |
| `--json` | Output in JSON format |
| `--text` | Output in text format (default) |
| `-r, --report` | Generate `tail_compliance_report.txt` in project root |
| `-o, --output FILE` | Write output to FILE |
| `-p, --prefix NAME` | Override auto-detected project prefix |
| `-h, --help` | Show help |

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All checks passed |
| 1 | One or more checks failed |
| 2 | Configuration error (missing lakefile, files, etc.) |
| 3 | Build error (project not compiled) |

### Examples

```bash
# Verify current directory (default mode)
lake exe tailverify

# Verify a specific project
lake exe tailverify /path/to/project

# Strict mode verification
lake exe tailverify --strict

# Generate JSON for CI
lake exe tailverify --json

# Run with SafeVerify kernel verification
lake exe tailverify --safeverify

# Save report to file
lake exe tailverify --output report.txt
lake exe tailverify --report  # Creates tail_compliance_report.txt
```

---

## tailscaffold

Generate a new TAIL-compliant project structure.

### Usage

```bash
lake exe tailscaffold [--strict] <ProjectName>
```

### Options

| Option | Description |
|--------|-------------|
| `--strict` | Create strict mode project (no Definitions/ folder) |
| `-h, --help` | Show help |

### Examples

```bash
# Default mode (with Definitions/)
lake exe tailscaffold MyTheorem

# Strict mode (Mathlib only)
lake exe tailscaffold --strict MyTheorem
```

### Generated Structure

**Default mode:**
```
MyTheorem/
├── MyTheorem/
│   ├── MainTheorem.lean
│   ├── Definitions/
│   │   └── Types.lean
│   ├── ProofOfMainTheorem.lean
│   └── Proofs/
│       └── Support.lean
├── lakefile.toml
└── lean-toolchain
```

**Strict mode:**
```
MyTheorem/
├── MyTheorem/
│   ├── MainTheorem.lean
│   ├── ProofOfMainTheorem.lean
│   └── Proofs/
│       └── Support.lean
├── lakefile.toml
└── lean-toolchain
```

---

## Example Output

### Passing Project

```
================================================================================
TAIL STANDARD COMPLIANCE REPORT
Project: MyProject
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
  Structure
    [PASS] Structure

  Trust Tier
    [PASS] Trust Tier

  Import Discipline
    [PASS] Import Discipline

================================================================================
RESULT: PROJECT MEETS TEMPLATE EXPECTATIONS
================================================================================
```

### Failing Project

```
================================================================================
TAIL STANDARD COMPLIANCE REPORT
Project: FailingProject
Tool: TAIL v0.1
================================================================================
...

CHECKS
--------------------------------------------------------------------------------
  Structure
    [PASS] Structure

  Trust Tier
    [FAIL] Trust Tier
           - FailingProject.Proofs.Helper: def badDef does not return Prop
           - FailingProject.Proofs.Helper: inductive BadStructure (not allowed)

  Import Discipline
    [FAIL] Import Discipline
           MainTheorem.lean import violations:
             - FailingProject.Proofs.Helper (project import not allowed)

================================================================================
RESULT: PROJECT FAILS TO MEET TEMPLATE EXPECTATIONS
================================================================================
```
