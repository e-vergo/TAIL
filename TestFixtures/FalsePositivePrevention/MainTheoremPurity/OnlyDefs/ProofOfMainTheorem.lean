module

public import TestFixtures.FalsePositivePrevention.MainTheoremPurity.OnlyDefs.MainTheorem

import all TestFixtures.FalsePositivePrevention.MainTheoremPurity.OnlyDefs.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := trivial
