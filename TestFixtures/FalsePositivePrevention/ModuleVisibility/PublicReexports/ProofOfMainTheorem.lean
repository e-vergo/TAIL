module

public import TestFixtures.FalsePositivePrevention.ModuleVisibility.PublicReexports.MainTheorem

import all TestFixtures.FalsePositivePrevention.ModuleVisibility.PublicReexports.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := trivial
