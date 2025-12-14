module

public import TestFixtures.ViolationDetection.ProofMinimality.ExtraDefinition.MainTheorem

import all TestFixtures.ViolationDetection.ProofMinimality.ExtraDefinition.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: extra definition
def helper : Nat := 42

theorem mainTheorem : StatementOfTheorem := trivial
