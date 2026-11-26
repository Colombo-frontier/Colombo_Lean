import FreshGradientMinimax.RobinOptimizerBounds

/-! Uniform increments of the endpoint Green columns. These bounds ensure
that the exact quadratic optimizer lies in the Huber quadratic region. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinSequence_increment {n : ℕ} (hn : 0 < n) (i : ℕ) :
    robinSequence n (i + 1) - robinSequence n i =
      robinStep n ^ 2 / 2 * robinSequence n i + Real.sinh (robinTheta n) *
        (Real.sinh ((i : ℝ) * robinTheta n) + robinSlope n * Real.cosh ((i : ℝ) * robinTheta n)) := by
  unfold robinSequence
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.cosh_add, Real.sinh_add,
    robinTheta_cosh hn]
  ring

theorem robinSequence_increment_bound {n i : ℕ} (hn : 10 ≤ n) (hi : i ≤ n) :
    robinSequence n (i + 1) - robinSequence n i ≤ 4 * robinStep n := by
  have hp := robin_parameters_bounds hn
  have hr := (robinStep_pos (n := n) (by omega)).le
  have hr1 : robinStep n ≤ 1 / 10 := by
    unfold robinStep
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have hu := robinSequence_le_three hn hi
  have hu0 := (show (0 : ℝ) ≤ 1 by norm_num).trans (robinSequence_ge_one hn i)
  have hf := robinSequence_function_bounds hn hi
  have hh := mul_le_mul hp.2.2.2.2 hf.1 (Real.cosh_pos _).le (by norm_num : (0 : ℝ) ≤ 21 / 20)
  have hv : Real.sinh ((i : ℝ) * robinTheta n) + robinSlope n * Real.cosh ((i : ℝ) * robinTheta n) ≤ 72 / 25 := by
    linarith only [hf.2, hh]
  have hv0 : 0 ≤ Real.sinh ((i : ℝ) * robinTheta n) + robinSlope n * Real.cosh ((i : ℝ) * robinTheta n) := by
    have ht := Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (robinTheta_pos (n := n) (by omega)).le)
    have hslope : 0 ≤ robinSlope n := (show (0 : ℝ) ≤ 1 by norm_num).trans hp.2.2.2.1
    positivity
  have h1 := mul_le_mul_of_nonneg_left hu (show 0 ≤ robinStep n ^ 2 / 2 by positivity)
  have h2 := mul_le_mul hp.2.2.1 hv hv0 (show 0 ≤ (11 / 10) * robinStep n by positivity)
  have hr2 := mul_le_mul_of_nonneg_left hr1 hr
  rw [robinSequence_increment (by omega)]
  nlinarith only [h1, h2, hr2, hr]

theorem robinBoundaryDenominator_gt_step {n : ℕ} (hn : 10 ≤ n) :
    robinStep n < robinBoundaryDenominator n := by
  have h := robinBoundaryDenominator_diagonal hn
  have hu := robinSequence_ge_one hn (n - 1)
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have he : (n : ℝ) * robinStep n = 1 := by unfold robinStep; exact mul_inv_cancel₀ hN.ne'
  nlinarith only [h, hu, he, hN]

theorem robinGreen_increment_bound {n i : ℕ} (hn : 10 ≤ n) (hi : i ≤ n) :
    |robinSequence n (i + 1) / robinBoundaryDenominator n -
      robinSequence n i / robinBoundaryDenominator n| ≤ 4 := by
  have hd := robinBoundaryDenominator_pos hn
  have hmono := robinSequence_monotone hn (show i ≤ i + 1 by omega)
  rw [← sub_div, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hmono) hd.le)]
  apply (div_le_iff₀ hd).mpr
  exact (robinSequence_increment_bound hn hi).trans
    (mul_le_mul_of_nonneg_left (robinBoundaryDenominator_gt_step hn).le (by norm_num))

theorem robinInverse_last_increment {n : ℕ} (hn : 10 ≤ n + 2) (i : Fin (n + 1)) :
    |robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i.succ -
      robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i.castSucc| ≤ 4 := by
  rw [robinInverse_last hn]
  simp only [robinGreenLast_apply, Fin.val_succ, Fin.coe_castSucc]
  exact robinGreen_increment_bound hn (by omega)

theorem robinInverse_first_increment {n : ℕ} (hn : 10 ≤ n + 2) (i : Fin (n + 1)) :
    |robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i.succ -
      robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i.castSucc| ≤ 4 := by
  rw [robinInverse_first hn]
  simp only [robinGreenFirst_apply, Fin.val_succ, Fin.coe_castSucc]
  rw [show n + 2 - 1 - (i.val + 1) = n - i.val by omega,
    show n + 2 - 1 - i.val = (n - i.val) + 1 by omega, abs_sub_comm]
  exact robinGreen_increment_bound hn (by omega)

end FreshGradientMinimax
