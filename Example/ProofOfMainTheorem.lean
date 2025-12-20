module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Example.MainTheorem
import Example.Proofs.helper_lemmas

namespace Example

@[expose] public section

/-- Proof of Nicomachus's Theorem using helper lemmas -/
theorem mainTheorem : StatementOfTheorem := fun n => by
  rw [sum_cubes_eq, sum_range_eq]

end

end Example
