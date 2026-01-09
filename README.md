# TAIL
**T**emplate for **AI**-generated **L**ean

A verification tool that enforces trust tier separation for AI-generated Lean proofs.

## The TAIL Standard

TAIL enforces a two-tier trust model:

| Tier | Files | Constraint |
|------|-------|------------|
| **Human Review** | MainTheorem.lean, Definitions/ | No restrictions - reviewer checks all |
| **Machine Verified** | ProofOfMainTheorem.lean, Proofs/ | Only Prop-valued declarations allowed |

The key principle: non-Prop declarations (structures, inductives, data-returning defs) **must** be in the human-review tier. This ensures a reviewer only needs to validate a small surface area to confirm the formalization is sound.

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
lake exe tailverify [dir]             # Verify a project
lake exe tailverify --strict [dir]    # Strict mode (no Definitions/)
lake exe tailverify --safeverify      # Enable SafeVerify kernel verification
lake exe tailverify --json            # JSON output for CI
lake exe tailscaffold ProjectName     # Create new project
```

## Documentation

- [The TAIL Standard](docs/standard.md) - Philosophy, modes, trust tiers
- [Verification Checks](docs/checks.md) - 3 core checks + optional SafeVerify
- [Project Structure](docs/project-structure.md) - File layouts and examples
- [CLI Reference](docs/cli-reference.md) - Full command reference
- [Integration Guide](docs/integration.md) - Adding TAIL to your project

## License

Apache 2.0
