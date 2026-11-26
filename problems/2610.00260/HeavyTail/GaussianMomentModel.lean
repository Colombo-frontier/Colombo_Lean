import HeavyTail.GaussianMixedExp

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace HeavyTail.GaussianEstimates

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem directional_power_integrable {ξ : Ω → E} (hξ : Measurable ξ)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (v : E) :
    Integrable (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p) P := by
  have hi2 : Integrable (fun ω => ⟪v, ξ ω⟫_ℝ ^ 2) P := by
    apply (h2.const_mul (‖v‖ ^ 2)).mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hn := abs_real_inner_le_norm v (ξ ω)
        nlinarith [sq_abs ⟪v, ξ ω⟫_ℝ, abs_nonneg ⟪v, ξ ω⟫_ℝ,
          norm_nonneg v, norm_nonneg (ξ ω)]
  apply ((integrable_const (1 : ℝ)).add hi2).mono'
  · apply Measurable.aestronglyMeasurable
    exact (Real.continuous_rpow_const hp).measurable.comp (by fun_prop)
  · exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      simp only [Pi.add_apply]
      by_cases hx : |⟪v, ξ ω⟫_ℝ| ≤ 1
      · have hh := Real.rpow_le_one (abs_nonneg _) hx hp
        linarith [sq_nonneg ⟪v, ξ ω⟫_ℝ]
      · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hp2
        rw [Real.rpow_two, sq_abs] at hh
        linarith

theorem unit_direction_bound {ξ : Ω → E} {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s)
    (hweak : ∀ v : E, ‖v‖ = 1 → (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ s ^ p)
    (v : E) : (∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P) ≤ (s * ‖v‖) ^ p := by
  by_cases hv : v = 0
  · simp [hv, Real.zero_rpow hp.ne']
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]
    have hvw : ‖v‖ • w = v := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have he : (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p) =
        (fun ω => ‖v‖ ^ p * |⟪w, ξ ω⟫_ℝ| ^ p) := by
      funext ω
      conv_lhs => rw [← hvw, real_inner_smul_left]
      rw [abs_mul, abs_of_nonneg (norm_nonneg v),
        Real.mul_rpow (norm_nonneg v) (abs_nonneg ⟪w, ξ ω⟫_ℝ)]
    rw [he, integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hweak w hw) (Real.rpow_nonneg (norm_nonneg v) p)
    rw [Real.mul_rpow hs (norm_nonneg v)]
    simpa only [mul_comm] using hh

end HeavyTail.GaussianEstimates
