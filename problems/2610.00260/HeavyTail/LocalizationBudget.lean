import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The geometric summation underlying manuscript Lemma `lem:phase-sum`.
This module proves the summation itself; it does not assume or certify a stochastic
optimization primitive or its stage budgets. -/
namespace HeavyTail
open scoped BigOperators

theorem geometric_confidence_sum {r ell b : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => r ^ (m + 1) * (ell + (m + 1 : ℕ) * b))
      (r / (1 - r) * ell + r / (1 - r) ^ 2 * b) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h0 := (hasSum_geometric_of_norm_lt_one hr).mul_left r
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hr)
  have hshift : HasSum (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * r ^ (m + 1))
      (r / (1 - r) ^ 2) := by
    have hs := (hasSum_nat_add_iff' 1).mpr h1
    simpa using hs
  convert (h0.mul_right ell).add (hshift.mul_right b) using 1
  · ext m
    simp only [pow_succ]
    ring

theorem finite_geometric_confidence_bound {r ell b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hell : 0 ≤ ell) (hb : 0 ≤ b) (N : ℕ) :
    (∑ m ∈ Finset.range N, r ^ (m + 1) * (ell + (m + 1 : ℕ) * b)) ≤
      r / (1 - r) * ell + r / (1 - r) ^ 2 * b := by
  have h := geometric_confidence_sum (ell := ell) (b := b) hr0 hr1
  rw [← h.tsum_eq]
  exact Summable.sum_le_tsum (Finset.range N)
    (fun m _ => mul_nonneg (pow_nonneg hr0 _) (by positivity)) h.summable

theorem finite_geometric_confidence_uniform {r ell b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hell : 1 ≤ ell) (hb : 0 ≤ b) (N : ℕ) :
    (∑ m ∈ Finset.range N, r ^ (m + 1) * (ell + (m + 1 : ℕ) * b)) ≤
      (r / (1 - r) + r / (1 - r) ^ 2 * b) * ell := by
  calc
    _ ≤ r / (1 - r) * ell + r / (1 - r) ^ 2 * b :=
      finite_geometric_confidence_bound hr0 hr1 (by linarith) hb N
    _ ≤ _ := by
      have hn : 0 ≤ r / (1 - r) ^ 2 * b := by positivity
      nlinarith

/-- The exact dyadic series displayed in the proof of `lem:phase-sum`. -/
theorem dyadic_confidence_sum {γ ell : ℝ} (hγ : 0 < γ) :
    HasSum (fun m : ℕ => (2 : ℝ) ^ (-γ * (m + 1 : ℕ)) *
      (ell + (m + 1 : ℕ) * Real.log 2))
      ((2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) * ell +
       (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) ^ 2 * Real.log 2) := by
  simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] using
    (geometric_confidence_sum (ell := ell) (b := Real.log 2)
      (Real.rpow_nonneg (by norm_num) (-γ))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)))

/-- The summation constant is independent of the number of localization stages. -/
theorem dyadic_confidence_uniform {γ ell : ℝ} (hγ : 0 < γ) (hell : 1 ≤ ell) (N : ℕ) :
    (∑ m ∈ Finset.range N, (2 : ℝ) ^ (-γ * (m + 1 : ℕ)) *
      (ell + (m + 1 : ℕ) * Real.log 2)) ≤
      ((2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) +
       (2 : ℝ) ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) ^ 2 * Real.log 2) * ell := by
  simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] using
    finite_geometric_confidence_uniform
      (Real.rpow_nonneg (by norm_num) (-γ))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ))
      hell (Real.log_nonneg (by norm_num)) N

end HeavyTail
