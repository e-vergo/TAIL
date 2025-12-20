module

public import Mathlib.Data.Nat.GCD.Basic

namespace DefaultExample

@[expose] public section

/-- A Pythagorean triple (a, b, c) satisfying a² + b² = c² -/
structure PythagoreanTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  pythagorean : a ^ 2 + b ^ 2 = c ^ 2

/-- A Pythagorean triple is primitive if gcd(a, b, c) = 1 -/
def PythagoreanTriple.isPrimitive (t : PythagoreanTriple) : Prop :=
  Nat.gcd t.a (Nat.gcd t.b t.c) = 1

/-- The standard parametrization: given m > n, produces (m² - n², 2mn, m² + n²) -/
structure EuclidParams where
  m : ℕ
  n : ℕ
  h_pos : 0 < n
  h_lt : n < m

end

end DefaultExample
