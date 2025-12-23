# Integration Guide

## Option 1: Run from TAIL Repository

Clone and build TAIL once, then verify any project:

```bash
# Clone and build TAIL
git clone https://github.com/e-vergo/TAIL.git
cd TAIL
lake exe cache get
lake build

# Verify any project
lake exe tailverify /path/to/your/project

# Verify in strict mode
lake exe tailverify --strict /path/to/your/project
```

## Option 2: Add as Dependency

Add TAIL as a dependency in your project's `lakefile.lean`:

```lean
import Lake
open Lake DSL

package MyProject where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require TAIL from git
  "https://github.com/e-vergo/TAIL.git"

@[default_target]
lean_lib MyProject where
```

Then run:

```bash
lake update
lake build
lake exe tailverify
```

## CI Integration

### GitHub Actions Example

```yaml
name: TAIL Verification

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install elan
        run: |
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH

      - name: Build project
        run: |
          lake exe cache get
          lake build

      - name: Clone TAIL
        run: |
          git clone https://github.com/e-vergo/TAIL.git /tmp/TAIL
          cd /tmp/TAIL
          lake exe cache get
          lake build

      - name: Verify TAIL compliance
        run: |
          cd /tmp/TAIL
          lake exe tailverify $GITHUB_WORKSPACE --json > /tmp/tail_report.json
          cat /tmp/tail_report.json

      - name: Check result
        run: |
          cd /tmp/TAIL
          lake exe tailverify $GITHUB_WORKSPACE
```

### JSON Output for CI

Use `--json` for machine-readable output:

```bash
lake exe tailverify --json > tail_report.json
```

The JSON includes:
- `result`: "VERIFIED" or "FAILED"
- `checks`: Array of check results
- `stats`: Line counts and review burden
- `warnings`: Semantic risk warnings

## Test Fixtures

The TAIL repository includes test fixtures for reference:

| Fixture | Mode | Result |
|---------|------|--------|
| `TestFixtures/PassAll` | default | Passes all checks |
| `TestFixtures/PassAllStrict` | strict | Passes all checks |
| `TestFixtures/FailAll` | default | Fails multiple checks |
| `TestFixtures/FailAllStrict` | strict | Fails multiple checks |

Run them:

```bash
lake exe tailverify TestFixtures/PassAll
lake exe tailverify --strict TestFixtures/PassAllStrict
```

## Creating a New Project

Use `tailscaffold` to generate a compliant project structure:

```bash
# Default mode (with Definitions/)
lake exe tailscaffold MyTheorem
cd MyTheorem
lake update
lake exe cache get

# Edit your files...
lake build
lake exe tailverify
```

See [Project Structure](project-structure.md) for details on the generated files.
