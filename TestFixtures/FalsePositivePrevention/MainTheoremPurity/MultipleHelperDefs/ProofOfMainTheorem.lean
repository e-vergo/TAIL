module

public import TestFixtures.FalsePositivePrevention.MainTheoremPurity.MultipleHelperDefs.MainTheorem

import all TestFixtures.FalsePositivePrevention.MainTheoremPurity.MultipleHelperDefs.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := by
  unfold StatementOfTheorem helperDef1 helperDef2
  exact Nat.lt_succ_self 42
