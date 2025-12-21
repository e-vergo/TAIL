module

public import Mathlib.Data.Nat.GCD.Basic
public import PassAll.MainTheorem
public import PassAll.Definitions.PythagoreanTriple
import PassAll.Proofs.EuclidFormula

namespace PassAll

@[expose] public section

/-- Proof of Euclid's Formula: the parametrization (m² - n², 2mn, m² + n²)
    always produces a valid Pythagorean triple. -/
theorem mainTheorem : StatementOfTheorem := fun p =>
  euclid_identity_nat p.h_lt

end

end PassAll
