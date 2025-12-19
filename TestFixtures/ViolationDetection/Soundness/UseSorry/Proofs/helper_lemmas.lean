module

import Mathlib.Tactic

open Finset

/-- Product of consecutive naturals is even -/
lemma two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  sorry

/-- Sum of first n+1 naturals equals n(n+1)/2 -/
lemma sum_range_eq (n : ℕ) : ∑ k ∈ range (n + 1), k = n * (n + 1) / 2 := by
  have h := sum_range_id_mul_two (n + 1)
  simp only [add_tsub_cancel_right] at h
  have hdiv := two_dvd_mul_succ n
  obtain ⟨m, hm⟩ := hdiv
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have : (∑ i ∈ range (n + 1), i) * 2 = 2 * m := by rw [← hm, h]; ring
  linarith

/--Key algebraic step for sum of cubes induction. -/
lemma sum_cubes_step (n : ℕ) :
    (n * (n + 1) / 2) ^ 2 + (n + 1) ^ 3 = ((n + 1) * (n + 2) / 2) ^ 2 := by
  sorry

/-- Sum of cubes equals square of sum (closed form) -/
lemma sum_cubes_eq (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    exact sum_cubes_step n
