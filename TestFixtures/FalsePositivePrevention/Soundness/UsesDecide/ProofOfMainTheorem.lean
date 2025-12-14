module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesDecide.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesDecide.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := by
  unfold StatementOfTheorem
  decide
