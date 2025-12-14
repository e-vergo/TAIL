module

public import TestFixtures.ViolationDetection.Soundness.UseNativeDecide.MainTheorem

import all TestFixtures.ViolationDetection.Soundness.UseNativeDecide.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: uses native_decide
theorem mainTheorem : StatementOfTheorem := by
  unfold StatementOfTheorem
  native_decide
