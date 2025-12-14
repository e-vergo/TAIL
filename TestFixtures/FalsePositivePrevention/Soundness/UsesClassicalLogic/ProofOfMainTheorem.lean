module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesClassicalLogic.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesClassicalLogic.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun p => Classical.em p
