module

public import Example.MainTheorem

import all Example.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun n => by
  rw [sum_cubes_eq, sum_range_eq]
