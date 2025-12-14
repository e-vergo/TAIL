module

public import TestFixtures.ViolationDetection.Soundness.CustomAxiom.MainTheorem

import all TestFixtures.ViolationDetection.Soundness.CustomAxiom.Proofs.helper_lemmas

@[expose] public section

-- VIOLATION: custom axiom
axiom myCustomAxiom : ∀ n : Nat, n < n + 1

theorem mainTheorem : StatementOfTheorem := myCustomAxiom
