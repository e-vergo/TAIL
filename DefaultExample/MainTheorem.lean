module

public import Mathlib.Data.Nat.GCD.Basic
public import DefaultExample.Definitions.PythagoreanTriple

namespace DefaultExample

@[expose] public section

/-- Euclid's Formula for Pythagorean Triples:

For any integers m > n > 0, the triple (m² - n², 2mn, m² + n²)
forms a Pythagorean triple.

This is the foundational result showing that the Euclidean parametrization
always produces valid Pythagorean triples.
-/
def StatementOfTheorem : Prop :=
  ∀ (p : EuclidParams),
    let a := p.m ^ 2 - p.n ^ 2
    let b := 2 * p.m * p.n
    let c := p.m ^ 2 + p.n ^ 2
    a ^ 2 + b ^ 2 = c ^ 2

end

end DefaultExample
