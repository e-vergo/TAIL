module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Main Theorem Statement

**Nicomachus's Theorem**: The sum of the first n cubes equals the square of the sum
of the first n natural numbers.

$$1^3 + 2^3 + \cdots + n^3 = (1 + 2 + \cdots + n)^2$$

This beautiful identity was known to the ancient Greeks and has many proofs,
including combinatorial, algebraic, and inductive approaches.

Per the Kim Morrison Standard:
- This file imports ONLY from Mathlib (no project imports)
- Contains only the statement definition, no proofs
- A human reviewer can fully understand what is being claimed
-/

@[expose] public section

/-- **Nicomachus's Theorem**: The sum of cubes equals the square of the sum.

For any natural number n:
  0³ + 1³ + 2³ + ⋯ + n³ = (0 + 1 + 2 + ⋯ + n)²

Using Finset.range (n+1) = {0, 1, ..., n}, this states:
  ∑ k in range (n+1), k³ = (∑ k in range (n+1), k)²
-/
def StatementOfTheorem : Prop :=
  ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), k ^ 3) = (∑ k ∈ Finset.range (n + 1), k) ^ 2
