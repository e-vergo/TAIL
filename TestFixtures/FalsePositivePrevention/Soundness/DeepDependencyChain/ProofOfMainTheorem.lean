module

public import TestFixtures.FalsePositivePrevention.Soundness.DeepDependencyChain.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.DeepDependencyChain.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun n => ⟨Nat.add_zero n, Nat.zero_add n⟩
