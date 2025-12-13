import Lake
open Lake DSL

package KM_Inspect where
  version := v!"0.1.0"
  keywords := #["verification", "formal-methods", "lean4"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean4checker from git
  "https://github.com/leanprover/lean4checker"

@[default_target]
lean_lib KM_Inspect where
  globs := #[.submodules `KM_Inspect]

-- Kim Morrison verification executable
lean_exe kmverify where
  root := `KM_Inspect.Main
  supportInterpreter := true

-- Kim Morrison scaffolding tool
lean_exe kmscaffold where
  root := `KM_Inspect.Scaffold
  supportInterpreter := true
