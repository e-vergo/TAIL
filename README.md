# TAIL
**<u>T</u>** emplate for **<u>AI</u>** -generated **<u>L</u>** ean

A verification tool that reduces the review burden for AI-generated lean proofs. T

## The TAIL Standard

TAIL enforces a file structure that isolates declarations that don't require a proof burden, dividing project files into two trust tiers:

- **Human Review**: `MainTheorem.lean` + `Definitions/` — defines *what* is being proven and the new objects used to prove it
- **Machine Verified**: `ProofOfMainTheorem.lean` + `Proofs/` — Contains logical deductions based off of the defined objects

A reviewer only needs to validate the human review files to confirm that the formalization is sound.

## Quick Start

```bash
# Clone and build TAIL
git clone https://github.com/e-vergo/TAIL.git
cd TAIL
lake exe cache get
lake build

# Verify a project
lake exe tailverify /path/to/project

# Create a new TAIL-compliant project
lake exe tailscaffold MyTheorem
```

## Project Structure

```
ProjectName/
├── MainTheorem.lean            [HUMAN REVIEW]
├── Definitions/                [HUMAN REVIEW] (optional)
├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
└── Proofs/                     [MACHINE VERIFIED] (optional)
```

## CLI Usage

```bash
lake exe tailverify [dir]           # Verify a project
lake exe tailverify --strict [dir]  # Strict mode (no Definitions/)
lake exe tailverify --json          # JSON output for CI
lake exe tailscaffold ProjectName   # Create new project
```

## Documentation

- [The TAIL Standard](docs/standard.md) — Philosophy, modes, trust tiers
- [Verification Checks](docs/checks.md) — All 10 checks explained
- [Project Structure](docs/project-structure.md) — File layouts and examples
- [CLI Reference](docs/cli-reference.md) — Full command reference
- [Integration Guide](docs/integration.md) — Adding TAIL to your project

## License

Apache 2.0
