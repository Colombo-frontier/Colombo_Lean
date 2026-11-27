import Nonsmooth.EventBarycenter

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} [IsProbabilityMeasure μ] {V : α → E}

theorem event_mean_weighted_sum (hV : Integrable V μ) {A : Set α} (hAm : MeasurableSet A)
    (hA : μ A ≠ 0) (hAc : μ Aᶜ ≠ 0) :
    μ.real A • (∫ x, V x ∂μ[|A]) + μ.real Aᶜ • (∫ x, V x ∂μ[|Aᶜ]) = ∫ x, V x ∂μ := by
  have hp : μ.real A ≠ 0 := (ENNReal.toReal_pos hA (measure_ne_top _ _)).ne'
  have hq : μ.real Aᶜ ≠ 0 := (ENNReal.toReal_pos hAc (measure_ne_top _ _)).ne'
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    ← measureReal_def, smul_smul, mul_inv_cancel₀ hp, mul_inv_cancel₀ hq, one_smul]
  exact integral_add_compl hAm hV

theorem event_mean_complement (hV : Integrable V μ) (hmean : (∫ x, V x ∂μ) = 0)
    {A : Set α} (hAm : MeasurableSet A) (hA : μ A ≠ 0) (hAc : μ Aᶜ ≠ 0) :
    (∫ x, V x ∂μ[|A]) = -(μ.real Aᶜ / μ.real A) • (∫ x, V x ∂μ[|Aᶜ]) := by
  have hp : μ.real A ≠ 0 := (ENNReal.toReal_pos hA (measure_ne_top _ _)).ne'
  have h := event_mean_weighted_sum hV hAm hA hAc
  rw [hmean] at h
  have h' := congrArg (fun z : E => (μ.real A)⁻¹ • z) (eq_neg_of_add_eq_zero_left h)
  simpa only [smul_smul, inv_mul_cancel₀ hp, one_smul, smul_neg, neg_smul,
    div_eq_inv_mul] using h'

theorem event_barycenter_two_sided (hV : Integrable V μ) (hmean : (∫ x, V x ∂μ) = 0)
    {v K : ℝ} (hv : 0 < v) (hK : 0 < K)
    (hInt : ∀ u : E, Integrable (fun x => Real.exp ⟪u, V x⟫_ℝ) μ)
    (hMGF : ∀ u : E, (∫ x, Real.exp ⟪u, V x⟫_ℝ ∂μ) ≤ K * Real.exp (v * ‖u‖ ^ 2 / 2))
    {A : Set α} (hAm : MeasurableSet A) (hA : μ A ≠ 0) (hAc : μ Aᶜ ≠ 0) :
    ‖∫ x, V x ∂μ[|A]‖ ^ 2 ≤ min (2 * v * Real.log (K / μ.real A))
      ((μ.real Aᶜ / μ.real A) ^ 2 * (2 * v * Real.log (K / μ.real Aᶜ))) := by
  apply le_min (event_barycenter_of_exp_moments hV hv hK hInt hMGF A hA)
  rw [event_mean_complement hV hmean hAm hA hAc, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, neg_sq]
  exact mul_le_mul_of_nonneg_left
    (event_barycenter_of_exp_moments hV hv hK hInt hMGF Aᶜ hAc) (sq_nonneg _)

end
end Nonsmooth
