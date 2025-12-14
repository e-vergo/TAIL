module

public import TestFixtures.FalsePositivePrevention.ProofMinimality.WithInternalAux.MainTheorem

import all TestFixtures.FalsePositivePrevention.ProofMinimality.WithInternalAux.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := fun n =>
  match n with
  | 0 => rfl
  | n + 1 => rfl
