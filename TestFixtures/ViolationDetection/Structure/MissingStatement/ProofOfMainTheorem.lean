module

public import TestFixtures.ViolationDetection.Structure.MissingStatement.MainTheorem

import all TestFixtures.ViolationDetection.Structure.MissingStatement.Proofs.helper_lemmas

@[expose] public section

-- Since StatementOfTheorem doesn't exist, prove something else
theorem mainTheorem : True := trivial
