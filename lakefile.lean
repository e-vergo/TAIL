import Lake
open Lake DSL

package TAIL where
  version := v!"0.1.0"
  keywords := #["verification", "formal-methods", "lean4"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
    -- Note: experimental.module is no longer required as of Lean 4.27+
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean4checker from git
  "https://github.com/leanprover/lean4checker"

@[default_target]
lean_lib TAIL where
  globs := #[.submodules `TAIL]

-- Kim Morrison verification executable
lean_exe tailverify where
  root := `TAIL.Main
  supportInterpreter := true

-- Kim Morrison scaffolding tool
lean_exe tailscaffold where
  root := `TAIL.Scaffold
  supportInterpreter := true

-- Example project demonstrating Kim Morrison Standard compliance
lean_lib Example where
  globs := #[.submodules `Example]

-- Test fixtures for verification checks
lean_lib TestFixtures where
  globs := #[.submodules `TestFixtures]

-- Test harness executable
lean_exe tailtest where
  root := `TAIL.Test
  supportInterpreter := true
