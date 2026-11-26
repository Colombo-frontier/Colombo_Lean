import FreshGradientMinimax.RobinCoefficients

/-! The interior recurrence and both Robin boundary equations of the explicit
Green column. Indices here are zero based. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinSlope_mul_sinh {n : ℕ} (hn : 0 < n) :
    robinSlope n * Real.sinh (robinTheta n) = robinBoundaryShift n := by
  unfold robinSlope
  exact div_mul_cancel₀ _ (Real.sinh_pos_iff.mpr (robinTheta_pos hn)).ne'

theorem robinSequence_one {n : ℕ} (hn : 0 < n) :
    robinSequence n 1 = 1 + robinStep n + robinStep n ^ 2 := by
  simp only [robinSequence, Nat.cast_one, one_mul, robinTheta_cosh hn,
    robinSlope_mul_sinh hn, robinBoundaryShift]
  ring

theorem robinSequence_recurrence {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (robinStep n ^ 2 + 2) * robinSequence n (i + 1) -
      robinSequence n i - robinSequence n (i + 2) = 0 := by
  have hc : Real.cosh ((i : ℝ) * robinTheta n) +
      Real.cosh (((i : ℝ) + 2) * robinTheta n) =
      2 * Real.cosh (robinTheta n) * Real.cosh (((i : ℝ) + 1) * robinTheta n) := by
    have h : Real.cosh ((((i : ℝ) + 1) * robinTheta n) - robinTheta n) +
        Real.cosh ((((i : ℝ) + 1) * robinTheta n) + robinTheta n) =
        2 * Real.cosh (robinTheta n) * Real.cosh (((i : ℝ) + 1) * robinTheta n) := by
      rw [Real.cosh_sub, Real.cosh_add]
      ring
    rw [show ((i : ℝ) + 1) * robinTheta n - robinTheta n = (i : ℝ) * robinTheta n by ring,
      show ((i : ℝ) + 1) * robinTheta n + robinTheta n = ((i : ℝ) + 2) * robinTheta n by ring] at h
    exact h
  have hs := path_sinh_recurrence (robinTheta n) (((i : ℝ) + 1) * robinTheta n)
  rw [show ((i : ℝ) + 1) * robinTheta n - robinTheta n = (i : ℝ) * robinTheta n by ring,
    show ((i : ℝ) + 1) * robinTheta n + robinTheta n = ((i : ℝ) + 2) * robinTheta n by ring] at hs
  rw [robinTheta_cosh hn] at hc hs
  simp only [robinSequence, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linear_combination -hc - robinSlope n * hs

theorem robinSequence_first_boundary {n : ℕ} (hn : 0 < n) :
    (robinStep n ^ 2 + 1 + robinStep n) * robinSequence n 0 - robinSequence n 1 = 0 := by
  rw [robinSequence_zero, robinSequence_one hn]
  ring

theorem robinSequence_last_boundary {n : ℕ} (hn : 2 ≤ n) :
    (robinStep n ^ 2 + 1 + robinStep n) * robinSequence n (n - 1) -
      robinSequence n (n - 2) = robinBoundaryDenominator n := by
  have he : ((n - 2 : ℕ) : ℝ) * robinTheta n =
      ((n - 1 : ℕ) : ℝ) * robinTheta n - robinTheta n := by
    rw [Nat.cast_sub hn, Nat.cast_sub (show 1 ≤ n by omega)]
    norm_num
    ring
  unfold robinBoundaryDenominator robinSequence
  rw [he, Real.cosh_sub, Real.sinh_sub, robinTheta_cosh (by omega)]
  unfold robinBoundaryShift
  ring

end FreshGradientMinimax
