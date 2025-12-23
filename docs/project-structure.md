# Project Structure

## Directory Layout

### Default Mode (with Definitions/)

```
ProjectName/
├── ProjectName/
│   ├── MainTheorem.lean            [HUMAN REVIEW]
│   ├── Definitions/                [HUMAN REVIEW]
│   │   └── Types.lean
│   ├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
│   └── Proofs/                     [MACHINE VERIFIED]
│       └── Helpers.lean
├── lakefile.lean
└── lean-toolchain
```

### Strict Mode (Mathlib only)

```
ProjectName/
├── ProjectName/
│   ├── MainTheorem.lean            [HUMAN REVIEW]
│   ├── ProofOfMainTheorem.lean     [MACHINE VERIFIED]
│   └── Proofs/                     [MACHINE VERIFIED]
│       └── Helpers.lean
├── lakefile.lean
└── lean-toolchain
```

## Required Names

All names are hardcoded per the TAIL Standard:

| Name | Purpose |
|------|---------|
| `MainTheorem.lean` | Statement file |
| `ProofOfMainTheorem.lean` | Proof file |
| `Definitions/` | Supporting types (default mode) |
| `Proofs/` | Helper lemmas (optional) |
| `ProjectName.StatementOfTheorem` | The proposition being proven |
| `ProjectName.mainTheorem` | The theorem proving it |

The project prefix is auto-detected from `lakefile.lean`.

## Example Files

### MainTheorem.lean (Default Mode)

```lean
module

public import Mathlib.Tactic
public import MyProject.Definitions.Types

namespace MyProject

@[expose] public section

/-- The theorem statement that will be proven. -/
def StatementOfTheorem : Prop :=
  ∀ n : ℕ, SomeProperty n

end

end MyProject
```

### MainTheorem.lean (Strict Mode)

```lean
module

public import Mathlib.Tactic

namespace MyProject

@[expose] public section

/-- The theorem statement using only Mathlib definitions. -/
def StatementOfTheorem : Prop :=
  ∀ n : ℕ, n + 0 = n

end

end MyProject
```

### ProofOfMainTheorem.lean

```lean
module

public import Mathlib.Tactic
public import MyProject.MainTheorem
import MyProject.Proofs.Helpers  -- Private (not re-exported)

namespace MyProject

@[expose] public section

theorem mainTheorem : StatementOfTheorem := by
  intro n
  exact helper_lemma n

end

end MyProject
```

### Definitions/Types.lean

```lean
module

public import Mathlib.Tactic

namespace MyProject

@[expose] public section

/-- A custom structure for the theorem statement. -/
structure MyStructure where
  value : ℕ
  property : value > 0

/-- A predicate used in the theorem. -/
def SomeProperty (n : ℕ) : Prop :=
  ∃ s : MyStructure, s.value = n

end

end MyProject
```

### Proofs/Helpers.lean

```lean
module

public import Mathlib.Tactic

namespace MyProject

public section

/-- A helper lemma for the main proof. -/
lemma helper_lemma (n : ℕ) : SomeProperty n := by
  sorry  -- Actual proof here

end

end MyProject
```

## Key Patterns

### Module Declaration

All files start with `module` to enable Lean 4.27+ module system features.

### Public vs Private Imports

```lean
public import Mathlib.Tactic       -- Re-exported to importers
public import MyProject.MainTheorem -- Re-exported
import MyProject.Proofs.Helpers     -- Private (not re-exported)
```

### @[expose] Attribute

The `@[expose]` attribute on `public section` ensures declarations are accessible:

```lean
@[expose] public section
-- declarations here are publicly visible
end
```

### Namespace Convention

Use a consistent namespace matching your project name:

```lean
namespace MyProject
-- all declarations here
end MyProject
```
