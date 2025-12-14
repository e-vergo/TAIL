module

public import TestFixtures.ViolationDetection.ProofMinimality.MultipleTheorems.MainTheorem

import all TestFixtures.ViolationDetection.ProofMinimality.MultipleTheorems.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := trivial

-- VIOLATION: extra theorem
theorem anotherTheorem : True := trivial
