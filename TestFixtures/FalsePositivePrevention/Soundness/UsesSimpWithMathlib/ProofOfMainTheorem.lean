module

public import TestFixtures.FalsePositivePrevention.Soundness.UsesSimpWithMathlib.MainTheorem

import all TestFixtures.FalsePositivePrevention.Soundness.UsesSimpWithMathlib.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun n => Nat.add_zero n
