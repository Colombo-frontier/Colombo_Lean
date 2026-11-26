import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Weighted projected-SGD telescope

This is the deterministic finite-sum argument in Appendix D of `2401.tex`.
Probability and conditional expectation are isolated in the recurrence
hypothesis; the entire weighted telescope below is axiom-free.
-/

open scoped BigOperators

namespace NoisyZO

lemma weighted_distance_telescope (R : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
      ((k + 1 : ℝ) * k * R (k + 1) -
        (k + 1 : ℝ) * (k + 2) * R (k + 2)) =
      -(n : ℝ) * (n + 1) * R (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_range_succ_cast (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Summation of the paper's rearranged one-step recurrence. -/
theorem biased_sgd_weighted_sum
    (n : ℕ) (R Δ : ℕ → ℝ) (B M : ℝ)
    (hM : 0 ≤ M)
    (hR : ∀ t, 0 ≤ R t)
    (hrec : ∀ k < n,
      Δ (k + 1) ≤
        ((k : ℝ) * R (k + 1) - (k + 2 : ℝ) * R (k + 2)) / 8 +
          B ^ 2 + 2 * M / (k + 2)) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) * Δ (k + 1) ≤
      (n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n := by
  have hterm : ∀ k ∈ Finset.range n,
      (k + 1 : ℝ) * Δ (k + 1) ≤
        (((k + 1 : ℝ) * k * R (k + 1) -
            (k + 1 : ℝ) * (k + 2) * R (k + 2)) / 8) +
          (k + 1 : ℝ) * B ^ 2 + 2 * M := by
    intro k hk
    have hkrec := hrec k (Finset.mem_range.mp hk)
    have hk1 : 0 ≤ (k + 1 : ℝ) := by positivity
    have hk2 : (k + 1 : ℝ) / (k + 2) ≤ 1 := by
      have : (0 : ℝ) < k + 2 := by positivity
      apply (div_le_one this).2
      norm_num
    calc
      (k + 1 : ℝ) * Δ (k + 1) ≤
          (k + 1 : ℝ) *
            (((k : ℝ) * R (k + 1) - (k + 2 : ℝ) * R (k + 2)) / 8 +
              B ^ 2 + 2 * M / (k + 2)) := by gcongr
      _ ≤ (((k + 1 : ℝ) * k * R (k + 1) -
              (k + 1 : ℝ) * (k + 2) * R (k + 2)) / 8) +
            (k + 1 : ℝ) * B ^ 2 + 2 * M := by
          have htwo :
              (k + 1 : ℝ) * (2 * M / (k + 2)) ≤ 2 * M := by
            calc
              (k + 1 : ℝ) * (2 * M / (k + 2)) =
                  2 * M * ((k + 1 : ℝ) / (k + 2)) := by ring
              _ ≤ 2 * M * 1 := by gcongr
              _ = 2 * M := by ring
          nlinarith
  have hsum := Finset.sum_le_sum hterm
  calc
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) * Δ (k + 1) ≤
        ∑ k ∈ Finset.range n,
          ((((k + 1 : ℝ) * k * R (k + 1) -
              (k + 1 : ℝ) * (k + 2) * R (k + 2)) / 8) +
            (k + 1 : ℝ) * B ^ 2 + 2 * M) := hsum
    _ = (-(n : ℝ) * (n + 1) * R (n + 1)) / 8 +
          (n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Finset.sum_div, weighted_distance_telescope]
      rw [← Finset.sum_mul, sum_range_succ_cast]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ (n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hn1 : 0 ≤ (n + 1 : ℝ) := by positivity
      have := hR (n + 1)
      have hprod : 0 ≤ (n : ℝ) * (n + 1) * R (n + 1) := by positivity
      have hneg : -(n : ℝ) * (n + 1) * R (n + 1) / 8 ≤ 0 := by
        nlinarith
      linarith

/-- The exact `B² + 4M/(n+1)` conclusion once convexity/Jensen supplies the
weighted-average comparison. -/
theorem biased_sgd_final_bound
    (n : ℕ) (hn : 0 < n) (weighted gap B M : ℝ)
    (hsum : weighted ≤ (n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n)
    (havg : gap ≤ 2 / ((n : ℝ) * (n + 1)) * weighted) :
    gap ≤ B ^ 2 + 4 * M / (n + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n + 1 : ℝ) := by positivity
  have hcoef : 0 < 2 / ((n : ℝ) * (n + 1)) := by positivity
  calc
    gap ≤ 2 / ((n : ℝ) * (n + 1)) * weighted := havg
    _ ≤ 2 / ((n : ℝ) * (n + 1)) *
        ((n : ℝ) * (n + 1) / 2 * B ^ 2 + 2 * M * n) := by gcongr
    _ = B ^ 2 + 4 * M / (n + 1) := by
      field_simp [ne_of_gt hnR, ne_of_gt hn1R]
      ring

end NoisyZO
