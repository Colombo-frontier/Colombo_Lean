import HeavyTail.GaussianWeighted

/-! The exceptional shifted-mean term in the scalar clipping estimate,
integrated against the actual finite-dimensional standard Gaussian law. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

def shiftedTail (t₀ y : ℝ) : ℝ :=
  if 1 / 2 < |t₀ + y| then Real.exp (2 * |t₀ + y|) * (t₀ + y) ^ 2 else 0

theorem shiftedTail_nonneg (t₀ y : ℝ) : 0 ≤ shiftedTail t₀ y := by
  unfold shiftedTail
  split_ifs <;> positivity

theorem shiftedTail_le {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8) (y : ℝ) :
    shiftedTail t₀ y ≤ 4 * Real.exp (1 / 4) * (Real.exp (2 * |y|) * y ^ 2) := by
  unfold shiftedTail
  split_ifs with h
  · have hab := abs_add_le t₀ y
    have hy : |t₀ + y| ≤ 2 * |y| := by linarith
    have hs : (t₀ + y) ^ 2 ≤ 4 * y ^ 2 := by
      nlinarith [sq_abs (t₀ + y), sq_abs y, abs_nonneg (t₀ + y), abs_nonneg y]
    have he : Real.exp (2 * |t₀ + y|) ≤ Real.exp (1 / 4) * Real.exp (2 * |y|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hm := mul_le_mul he hs (sq_nonneg (t₀ + y))
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    nlinarith
  · positivity

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem shiftedTail_integrable {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8) (d : E) :
    Integrable (fun z => shiftedTail t₀ ⟪d, z⟫_ℝ) (euclideanGaussianLaw E) := by
  apply ((gaussian_weighted_square_integrable E d d 2).const_mul (4 * Real.exp (1 / 4))).mono'
  · have hf : Measurable (fun z : E => shiftedTail t₀ ⟪d, z⟫_ℝ) := by
      unfold shiftedTail
      apply Measurable.ite
      · apply measurableSet_lt measurable_const
        fun_prop
      · fun_prop
      · fun_prop
    exact hf.aestronglyMeasurable
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (shiftedTail_nonneg _ _)]
      exact shiftedTail_le ht _

theorem gaussian_shifted_tail_bound {t₀ : ℝ} (ht : |t₀| ≤ 1 / 8) (d : E)
    (hd : 4 * ‖d‖ ^ 2 ≤ 1) :
    (∫ z, shiftedTail t₀ ⟪d, z⟫_ℝ ∂euclideanGaussianLaw E) ≤
      (4 * Real.exp (1 / 4) * (Real.exp 2 + 3 / 2)) * ‖d‖ ^ 2 := by
  have h := integral_mono (shiftedTail_integrable E ht d)
    ((gaussian_weighted_square_integrable E d d 2).const_mul (4 * Real.exp (1 / 4)))
    (fun z => shiftedTail_le ht ⟪d, z⟫_ℝ)
  rw [integral_const_mul] at h
  have hb := gaussian_weighted_square_uniform E d d (c := 2) (by norm_num at *; exact hd)
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * Real.exp (1 / 4))
  exact h.trans (by simpa only [mul_assoc] using hm)

end HeavyTail.GaussianEstimates
