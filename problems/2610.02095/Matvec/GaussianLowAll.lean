import Matvec.GaussianDistributionBounds

/-! Complete the uniform small-singular-value event in every positive
dimension. For the finitely many small dimensions a single inverse-Gram
diagonal marginal suffices; the large-dimensional argument is unchanged. -/
namespace Matvec
open MeasureTheory Matrix LowRank
noncomputable section

def gaussianLowProbability (a : ℝ) : ℝ :=
  min (smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank))
    (smallBallDensity * a / (2 * Real.sqrt (lowEventRank + 1 : ℝ)))

theorem gaussianLowProbability_pos {a : ℝ} (ha : 0 < a) :
    0 < gaussianLowProbability a := by
  have hc := smallBallDensity_pos
  have hr : (0 : ℝ) < lowEventRank := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) lowEventRank_ge_two)
  unfold gaussianLowProbability
  positivity

theorem gaussian_leastStretch_low_diagonal (n : ℕ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity * a / (2 * Real.sqrt (n + 1 : ℝ)) ≤
      (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | leastStretch (matrixEuclideanMap G) ≤ a / Real.sqrt (n + 1 : ℝ)} := by
  let u := a / Real.sqrt (n + 1 : ℝ)
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hs1 : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hu : 0 < u := div_pos ha hs
  have hu1 : u ≤ 1 := (div_le_one hs).mpr (ha1.trans hs1)
  let μ := iidMatrixLaw (n + 1) (n + 1) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  have hl := square_inverse_diagonal_lower n (Fin.last n) hu hu1
  have heq : smallBallDensity * u / 2 =
      smallBallDensity * a / (2 * Real.sqrt (n + 1 : ℝ)) := by dsimp [u]; ring
  rw [heq] at hl
  apply hl.trans
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [iidMatrixLaw_mulVec_injective_ae (n + 1) (n + 1) le_rfl
    (by norm_num : (1 : NNReal) ≠ 0)] with G hG
  intro hd
  have hdiag := psd_diagonal_nonneg (inverseGram_le_top G) (Fin.last n)
  have hdiag' : inverseGram G (Fin.last n) (Fin.last n) ≤
      inverseGramEigenvalue G (Fin.last n) := by
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, sub_nonneg] using hdiag
  have h := leastStretch_le_of_inverseGram_eigenvalue G (by omega) hG
    (Fin.last n) ((u ^ 2)⁻¹) (by positivity) (hd.trans hdiag')
  have hsqrt : (Real.sqrt ((u ^ 2)⁻¹))⁻¹ = u := by
    rw [Real.sqrt_inv, Real.sqrt_sq hu.le, inv_inv]
  rwa [hsqrt] at h

theorem gaussian_leastStretch_low_all (n : ℕ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    gaussianLowProbability a ≤
      (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | leastStretch (matrixEuclideanMap G) ≤ a / Real.sqrt (n + 1 : ℝ)} := by
  by_cases hn : lowEventRank ≤ n
  · exact (min_le_left _ _).trans (gaussian_leastStretch_low n hn ha ha1)
  · apply (min_le_right _ _).trans
    apply le_trans _ (gaussian_leastStretch_low_diagonal n ha ha1)
    have hnr : (n : ℝ) + 1 ≤ lowEventRank + 1 := by exact_mod_cast (by omega : n + 1 ≤ lowEventRank + 1)
    exact div_le_div_of_nonneg_left (by have := smallBallDensity_pos; positivity)
      (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnr) (by norm_num))

end
end Matvec
