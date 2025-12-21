module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PassAllStrict.MainTheorem
import PassAllStrict.Proofs.helper_lemmas

namespace PassAllStrict

@[expose] public section

/-- Proof of Nicomachus's Theorem using helper lemmas -/
theorem mainTheorem : StatementOfTheorem := fun n => by
  rw [sum_cubes_eq, sum_range_eq]

end

end PassAllStrict
