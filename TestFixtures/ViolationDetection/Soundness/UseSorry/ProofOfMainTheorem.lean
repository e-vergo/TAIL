module

public import TestFixtures.ViolationDetection.Soundness.UseSorry.MainTheorem

import all TestFixtures.ViolationDetection.Soundness.UseSorry.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: uses sorry
theorem mainTheorem : StatementOfTheorem := by
  intro n
  sorry
