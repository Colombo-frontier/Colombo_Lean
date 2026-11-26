import FreshGradientMinimax.RobinHyperbolic

/-! Bounds for the explicit endpoint Green-column coefficients. Their
identification with the actual inverse is proved in the Robin operator modules. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinBoundaryDenominator_pos {n : ℕ} (hn : 10 ≤ n) : 0 < robinBoundaryDenominator n := by
  have hr := robinStep_pos (show 0 < n by omega)
  have hu := robinSequence_ge_one hn (n - 1)
  have hh := (robin_parameters_bounds hn).2.2.2.1
  have hs := Real.sinh_pos_iff.mpr (robinTheta_pos (show 0 < n by omega))
  have ht : 0 ≤ ((n - 1 : ℕ) : ℝ) * robinTheta n :=
    mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (by omega)).le
  have hc := Real.cosh_pos (((n - 1 : ℕ) : ℝ) * robinTheta n)
  have hst := Real.sinh_nonneg_iff.mpr ht
  unfold robinBoundaryDenominator robinBoundaryShift
  positivity

theorem robinBoundaryDenominator_scaled_bound {n : ℕ} (hn : 10 ≤ n) :
    (n : ℝ) * robinBoundaryDenominator n ≤ 7 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hr := robinStep_pos (show 0 < n by omega)
  have hp := robin_parameters_bounds hn
  have hu := robinSequence_le_three hn (Nat.sub_le n 1)
  have hu0 : 0 ≤ robinSequence n (n - 1) := le_trans (by norm_num) (robinSequence_ge_one hn _)
  have hf := robinSequence_function_bounds hn (Nat.sub_le n 1)
  have ht : 0 ≤ ((n - 1 : ℕ) : ℝ) * robinTheta n := mul_nonneg (Nat.cast_nonneg _) (robinTheta_pos (n := n) (by omega)).le
  have hsn := Real.sinh_nonneg_iff.mpr ht
  have hhh := mul_le_mul hp.2.2.2.2 hf.1 (Real.cosh_pos _).le (by norm_num : (0 : ℝ) ≤ 21 / 20)
  have hv : Real.sinh (((n - 1 : ℕ) : ℝ) * robinTheta n) +
      robinSlope n * Real.cosh (((n - 1 : ℕ) : ℝ) * robinTheta n) ≤ 72 / 25 := by linarith
  have hv0 : 0 ≤ Real.sinh (((n - 1 : ℕ) : ℝ) * robinTheta n) +
      robinSlope n * Real.cosh (((n - 1 : ℕ) : ℝ) * robinTheta n) :=
    add_nonneg hsn (mul_nonneg (le_trans (by norm_num) hp.2.2.2.1) (Real.cosh_pos _).le)
  have he : (n : ℝ) * robinStep n = 1 := by unfold robinStep; exact mul_inv_cancel₀ hn0.ne'
  have hs : (n : ℝ) * Real.sinh (robinTheta n) ≤ 11 / 10 := by
    have h := mul_le_mul_of_nonneg_left hp.2.2.1 hn0.le
    nlinarith only [h, he]
  have hr1 : robinStep n ≤ 1 / 10 := by
    change (n : ℝ)⁻¹ ≤ 1 / 10
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have hd : (n : ℝ) * robinBoundaryShift n ≤ 21 / 20 := by
    have he' : (n : ℝ) * robinBoundaryShift n = 1 + robinStep n / 2 := by
      have he2 := congrArg (fun x : ℝ => x * robinStep n) he
      dsimp only at he2
      unfold robinBoundaryShift
      nlinarith only [he, he2]
    rw [he']
    linarith
  have h1 := mul_le_mul hd hu hu0 (by norm_num : (0 : ℝ) ≤ 21 / 20)
  have h2 := mul_le_mul hs hv hv0 (by norm_num : (0 : ℝ) ≤ 11 / 10)
  unfold robinBoundaryDenominator
  nlinarith only [h1, h2]

theorem robinBoundaryDenominator_diagonal {n : ℕ} (hn : 10 ≤ n) :
    robinSequence n (n - 1) < (n : ℝ) * robinBoundaryDenominator n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hr := robinStep_pos (show 0 < n by omega)
  have hs := Real.sinh_pos_iff.mpr (robinTheta_pos (show 0 < n by omega))
  have hu : 0 < robinSequence n (n - 1) := lt_of_lt_of_le (by norm_num) (robinSequence_ge_one hn _)
  have hh : 0 < robinSlope n := lt_of_lt_of_le (by norm_num) (robin_parameters_bounds hn).2.2.2.1
  have hsn := Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg (α := ℝ) (n - 1)) (robinTheta_pos (n := n) (by omega)).le)
  have hc := Real.cosh_pos (((n - 1 : ℕ) : ℝ) * robinTheta n)
  have he : (n : ℝ) * robinStep n = 1 := by unfold robinStep; exact mul_inv_cancel₀ hn0.ne'
  have hpos : 0 < (n : ℝ) * (robinStep n ^ 2 / 2) * robinSequence n (n - 1) := by positivity
  have hnon : 0 ≤ (n : ℝ) * Real.sinh (robinTheta n) *
      (Real.sinh (((n - 1 : ℕ) : ℝ) * robinTheta n) + robinSlope n * Real.cosh (((n - 1 : ℕ) : ℝ) * robinTheta n)) := by positivity
  have he' := congrArg (fun x : ℝ => x * robinSequence n (n - 1)) he
  dsimp only at he'
  unfold robinBoundaryDenominator robinBoundaryShift
  nlinarith only [hpos, hnon, he']

def robinA1 (n : ℕ) : ℝ := robinSequence n (n - 1) / ((n : ℝ) * robinBoundaryDenominator n)
def robinA2 (n : ℕ) : ℝ := 1 / ((n : ℝ) * robinBoundaryDenominator n)
def robinC (n : ℕ) : ℝ := 12 / robinA2 n
def robinSmallC (n : ℕ) : ℝ := robinC n * (1 + robinA2 n - robinA1 n) / 2

theorem robin_endpoint_coefficient_bounds {n : ℕ} (hn : 10 ≤ n) :
    1 / 7 ≤ robinA2 n ∧ robinA2 n ≤ robinA1 n ∧ robinA1 n < 1 := by
  have hd : 0 < (n : ℝ) * robinBoundaryDenominator n :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (robinBoundaryDenominator_pos hn)
  refine ⟨?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hd (robinBoundaryDenominator_scaled_bound hn)
  · exact div_le_div_of_nonneg_right (robinSequence_ge_one hn _) hd.le
  · exact (div_lt_one hd).mpr (robinBoundaryDenominator_diagonal hn)

theorem robin_coefficients_bounds {n : ℕ} (hn : 10 ≤ n) :
    12 ≤ robinC n ∧ robinC n ≤ 84 ∧ 0 < robinSmallC n ∧ robinSmallC n ≤ 42 := by
  have ha := robin_endpoint_coefficient_bounds hn
  have ha2 : 0 < robinA2 n := lt_of_lt_of_le (by norm_num) ha.1
  have hC : 12 ≤ robinC n := by
    unfold robinC
    exact (le_div_iff₀ ha2).mpr (by linarith)
  have hC' : robinC n ≤ 84 := by
    unfold robinC
    exact (div_le_iff₀ ha2).mpr (by linarith)
  refine ⟨hC, hC', ?_, ?_⟩
  · unfold robinSmallC
    exact div_pos (mul_pos (lt_of_lt_of_le (by norm_num) hC) (by linarith)) (by norm_num)
  · have hx : 1 + robinA2 n - robinA1 n ≤ 1 := by linarith
    have h := mul_le_of_le_one_right (le_trans (by norm_num) hC) hx
    unfold robinSmallC
    linarith

end FreshGradientMinimax

