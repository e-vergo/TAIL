module

public import TestFixtures.ViolationDetection.ModuleVisibility.WrongImportType.MainTheorem

-- VIOLATION: Should be import all, but using public import leaks helpers
public import TestFixtures.ViolationDetection.ModuleVisibility.WrongImportType.Proofs.helper_lemmas

@[expose] public section

theorem mainTheorem : StatementOfTheorem := trivial
