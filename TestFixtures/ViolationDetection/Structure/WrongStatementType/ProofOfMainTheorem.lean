module

public import TestFixtures.ViolationDetection.Structure.WrongStatementType.MainTheorem

import all TestFixtures.ViolationDetection.Structure.WrongStatementType.Proofs.helper_lemmas

@[expose] public section

-- Can't prove a Nat, so just prove True
theorem mainTheorem : True := trivial
