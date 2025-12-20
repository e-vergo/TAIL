module

public import Mathlib.Data.Nat.GCD.Basic
public import DefaultExample.MainTheorem
public import DefaultExample.Definitions.PythagoreanTriple
import DefaultExample.Proofs.EuclidFormula

namespace DefaultExample

@[expose] public section

/-- Proof of Euclid's Formula: the parametrization (m² - n², 2mn, m² + n²)
    always produces a valid Pythagorean triple. -/
theorem mainTheorem : StatementOfTheorem := fun p =>
  euclid_identity_nat p.h_lt

end

end DefaultExample
