module

public import TestFixtures.ViolationDetection.MainTheoremPurity.TheoremInStatement.MainTheorem

import all TestFixtures.ViolationDetection.MainTheoremPurity.TheoremInStatement.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := trivial
