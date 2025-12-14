module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesQuotient.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesQuotient.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := Quotient.sound rfl
