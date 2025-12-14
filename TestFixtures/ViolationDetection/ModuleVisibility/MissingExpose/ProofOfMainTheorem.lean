module

public import TestFixtures.ViolationDetection.ModuleVisibility.MissingExpose.MainTheorem

import all TestFixtures.ViolationDetection.ModuleVisibility.MissingExpose.Proofs.helper_lemmas

-- VIOLATION: Missing @[expose] public section
-- mainTheorem might not be visible to importers
theorem mainTheorem : StatementOfTheorem := trivial
