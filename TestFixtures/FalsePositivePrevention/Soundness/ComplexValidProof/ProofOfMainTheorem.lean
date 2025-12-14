module

public import TestFixtures.FalsePositivePrevention.Soundness.ComplexValidProof.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.ComplexValidProof.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun n => ⟨Nat.add_zero n, Nat.zero_add n⟩
