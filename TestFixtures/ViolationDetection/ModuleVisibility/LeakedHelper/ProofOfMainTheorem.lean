module

public import TestFixtures.ViolationDetection.ModuleVisibility.LeakedHelper.MainTheorem

import all TestFixtures.ViolationDetection.ModuleVisibility.LeakedHelper.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: this def is in public section and will be exported
def leakedHelper : Nat := 42

theorem mainTheorem : StatementOfTheorem := trivial
