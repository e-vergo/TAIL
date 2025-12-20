module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Example

@[expose] public section

/-- Nicomachus's Theorem:

For any natural number n:
  1³ + 2³ + ⋯ + n³ = (1 + 2 + ⋯ + n)²

-/
def StatementOfTheorem : Prop :=
  ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), k ^ 3) = (∑ k ∈ Finset.range (n + 1), k) ^ 2

end

end Example
