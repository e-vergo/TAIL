module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesStandardAxioms.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesStandardAxioms.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun p q hpq => propext hpq
