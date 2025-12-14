module

public import TestFixtures.ViolationDetection.ProofMinimality.ZeroTheorems.MainTheorem

import all TestFixtures.ViolationDetection.ProofMinimality.ZeroTheorems.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: no theorems, only a def
def notATheorem : Nat := 42
