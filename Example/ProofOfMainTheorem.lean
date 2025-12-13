module

-- Public: re-exported to anyone who imports this module
public import Example.MainTheorem

-- Private: accessible here via `import all`, NOT re-exported to importers
import all Example.Proofs.helper_lemmas

/-!
# Proof of Nicomachus's Theorem

Per the Kim Morrison Standard:
- MainTheorem is publicly imported (re-exported)
- Supporting lemmas are imported with `import all` (private scope access, not re-exported)
- `import Example.ProofOfMainTheorem` adds exactly two declarations:
  `StatementOfTheorem` and `mainTheorem`
-/

@[expose] public section

open helper_lemmas

theorem mainTheorem : StatementOfTheorem := fun n => by
  rw [sum_cubes_eq, sum_range_eq]

end
