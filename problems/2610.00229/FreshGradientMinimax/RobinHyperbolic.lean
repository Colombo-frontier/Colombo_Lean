import FreshGradientMinimax.PathThetaBounds
import FreshGradientMinimax.GaussianPowerBounds

/-! Quantitative hyperbolic parameters for the original Robin chain in E.1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robin_hyperbolic_bounds {r θ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 10)
    (hθ : 0 < θ) (hc : Real.cosh θ = 1 + r ^ 2 / 2) :
    θ ≤ r ∧ r ≤ Real.sinh θ ∧ Real.sinh θ ≤ (11 / 10) * r ∧
      1 ≤ (r + r ^ 2 / 2) / Real.sinh θ ∧ (r + r ^ 2 / 2) / Real.sinh θ ≤ 21 / 20 := by
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
  have hs2 : Real.sinh θ ^ 2 = r ^ 2 + r ^ 4 / 4 := by rw [Real.sinh_sq, hc]; ring
  have hr2 : r ^ 2 ≤ 1 / 100 := by nlinarith
  have hr4 : r ^ 4 ≤ r ^ 2 / 100 := by
    have h := mul_le_mul_of_nonneg_right hr2 (sq_nonneg r)
    nlinarith only [h]
  have hsr : r ≤ Real.sinh θ := by nlinarith [sq_nonneg (r ^ 2)]
  have hst : Real.sinh θ ≤ (11 / 10) * r := by nlinarith
  have hd : Real.sinh θ ≤ r + r ^ 2 / 2 := by
    have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr.le 3
    nlinarith [sq_nonneg (r + r ^ 2 / 2)]
  refine ⟨?_, hsr, hst, (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hd), ?_⟩
  · have h := cosh_quadratic_lower hθ.le
    rw [hc] at h
    nlinarith
  · apply (div_le_iff₀ hs).mpr
    nlinarith only [hr1, hsr, hr, sq_nonneg (r - 1 / 20)]

theorem robin_cosh_one_bound : Real.cosh 1 ≤ 8 / 5 := by
  rw [Real.cosh_eq]
  nlinarith [exp_one_rational_bounds.2, exp_neg_one_le]

theorem robin_sinh_one_bound : Real.sinh 1 ≤ 6 / 5 := by
  have he : (4 / 11 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    apply (le_div_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [exp_one_rational_bounds.2]
  rw [Real.sinh_eq]
  nlinarith [exp_one_rational_bounds.2]

def robinStep (n : ℕ) : ℝ := (n : ℝ)⁻¹
def robinTheta (n : ℕ) : ℝ := pathTheta (robinStep n ^ 2) 1
def robinBoundaryShift (n : ℕ) : ℝ := robinStep n + robinStep n ^ 2 / 2
def robinSlope (n : ℕ) : ℝ := robinBoundaryShift n / Real.sinh (robinTheta n)
def robinSequence (n i : ℕ) : ℝ :=
  Real.cosh ((i : ℝ) * robinTheta n) + robinSlope n * Real.sinh ((i : ℝ) * robinTheta n)
def robinBoundaryDenominator (n : ℕ) : ℝ :=
  robinBoundaryShift n * robinSequence n (n - 1) + Real.sinh (robinTheta n) *
    (Real.sinh ((n - 1 : ℕ) * robinTheta n) + robinSlope n * Real.cosh ((n - 1 : ℕ) * robinTheta n))

theorem robinStep_pos {n : ℕ} (hn : 0 < n) : 0 < robinStep n := inv_pos.mpr (Nat.cast_pos.mpr hn)

theorem robinTheta_pos {n : ℕ} (hn : 0 < n) : 0 < robinTheta n :=
  pathTheta_pos (sq_pos_of_pos (robinStep_pos hn)) (by norm_num)

theorem robinTheta_cosh {n : ℕ} (hn : 0 < n) :
    Real.cosh (robinTheta n) = 1 + robinStep n ^ 2 / 2 := by
  rw [robinTheta, pathTheta_cosh (sq_pos_of_pos (robinStep_pos hn)) (by norm_num)]
  norm_num

theorem robin_parameters_bounds {n : ℕ} (hn : 10 ≤ n) :
    robinTheta n ≤ robinStep n ∧ robinStep n ≤ Real.sinh (robinTheta n) ∧
      Real.sinh (robinTheta n) ≤ (11 / 10) * robinStep n ∧ 1 ≤ robinSlope n ∧ robinSlope n ≤ 21 / 20 := by
  have hn0 : 0 < n := by omega
  apply robin_hyperbolic_bounds (robinStep_pos hn0) _ (robinTheta_pos hn0) (robinTheta_cosh hn0)
  change (n : ℝ)⁻¹ ≤ 1 / 10
  rw [← one_div]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10)
  exact_mod_cast hn

theorem robinSequence_zero (n : ℕ) : robinSequence n 0 = 1 := by simp [robinSequence]

theorem robinSequence_ge_one {n : ℕ} (hn : 10 ≤ n) (i : ℕ) : 1 ≤ robinSequence n i := by
  have hh : 0 ≤ robinSlope n := le_trans (by norm_num) (robin_parameters_bounds hn).2.2.2.1
  have hs : 0 ≤ Real.sinh ((i : ℝ) * robinTheta n) := Real.sinh_nonneg_iff.mpr
    (mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le)
  unfold robinSequence
  linarith [Real.one_le_cosh ((i : ℝ) * robinTheta n), mul_nonneg hh hs]

theorem robinSequence_argument_le {n i : ℕ} (hn : 10 ≤ n) (hi : i ≤ n) :
    (i : ℝ) * robinTheta n ≤ 1 := by
  have h1 := mul_le_mul_of_nonneg_left (robin_parameters_bounds hn).1 (Nat.cast_nonneg (α := ℝ) i)
  have h2 := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi : (i : ℝ) ≤ n) (robinStep_pos (n := n) (by omega)).le
  have he : (n : ℝ) * robinStep n = 1 := by
    unfold robinStep
    exact mul_inv_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega))
  exact h1.trans (h2.trans_eq he)

theorem robinSequence_function_bounds {n i : ℕ} (hn : 10 ≤ n) (hi : i ≤ n) :
    Real.cosh ((i : ℝ) * robinTheta n) ≤ 8 / 5 ∧ Real.sinh ((i : ℝ) * robinTheta n) ≤ 6 / 5 := by
  have ht := robinSequence_argument_le hn hi
  have ht0 : 0 ≤ (i : ℝ) * robinTheta n := mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le
  refine ⟨?_, (Real.sinh_le_sinh.mpr ht).trans robin_sinh_one_bound⟩
  apply le_trans (Real.cosh_le_cosh.mpr ?_) robin_cosh_one_bound
  simpa only [abs_of_nonneg ht0, abs_one] using ht

theorem robinSequence_le_three {n i : ℕ} (hn : 10 ≤ n) (hi : i ≤ n) : robinSequence n i ≤ 3 := by
  have hf := robinSequence_function_bounds hn hi
  have hh := (robin_parameters_bounds hn).2.2.2
  have hp := mul_le_mul hh.2 hf.2 (Real.sinh_nonneg_iff.mpr
    (mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le)) (by norm_num : (0 : ℝ) ≤ 21 / 20)
  unfold robinSequence
  linarith only [hf.1, hp]

end FreshGradientMinimax

