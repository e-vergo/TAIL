module

import Mathlib.Tactic

open Finset

/-- Product of consecutive naturals is even -/
lemma two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (2 * k + 1), by ring⟩
  · exact ⟨(2 * k + 1) * (k + 1), by ring⟩


axiom sum_range_eq (n : ℕ) : ∑ k ∈ range (n + 1), k = n * (n + 1) / 2

/-- Sum of first n+1 naturals equals n(n+1)/2 -/
-- lemma sum_range_eq (n : ℕ) : ∑ k ∈ range (n + 1), k = n * (n + 1) / 2 := by
--   have h := sum_range_id_mul_two (n + 1)
--   simp only [add_tsub_cancel_right] at h
--   have hdiv := two_dvd_mul_succ n
--   obtain ⟨m, hm⟩ := hdiv
--   rw [hm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
--   have : (∑ i ∈ range (n + 1), i) * 2 = 2 * m := by rw [← hm, h]; ring
--   linarith Key algebraic step for sum of cubes induction. -/
lemma sum_cubes_step (n : ℕ) :
    (n * (n + 1) / 2) ^ 2 + (n + 1) ^ 3 = ((n + 1) * (n + 2) / 2) ^ 2 := by
  obtain ⟨a, ha⟩ := two_dvd_mul_succ n
  obtain ⟨b, hb⟩ := two_dvd_mul_succ (n + 1)
  have ha' : n * (n + 1) / 2 = a := by
    rw [ha]; exact Nat.mul_div_cancel_left a (by norm_num)
  have hb' : (n + 1) * (n + 2) / 2 = b := by
    rw [hb]; exact Nat.mul_div_cancel_left b (by norm_num)
  rw [ha', hb']
  have hab : b = a + (n + 1) := by
    have eq1 : 2 * b = (n + 1) * (n + 2) := hb.symm
    have eq2 : 2 * a = n * (n + 1) := ha.symm
    have : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring
    linarith
  have cube_expand : (n + 1) ^ 3 = 2 * a * (n + 1) + (n + 1) ^ 2 := by
    have eq : n * (n + 1) = 2 * a := by linarith [ha.symm]
    nlinarith [sq_nonneg n, sq_nonneg a]
  calc a ^ 2 + (n + 1) ^ 3
      = a ^ 2 + (2 * a * (n + 1) + (n + 1) ^ 2) := by rw [cube_expand]
    _ = (a + (n + 1)) ^ 2 := by ring
    _ = b ^ 2 := by rw [hab]

/-- Sum of cubes equals square of sum (closed form) -/
lemma sum_cubes_eq (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    exact sum_cubes_step n
