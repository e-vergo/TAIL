module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesRflAndTrivial.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesRflAndTrivial.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := ⟨rfl, trivial⟩
