import Nonsmooth.GaussianAxialCap

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [mβ : MeasurableSpace β]
  [StandardBorelSpace β] [Nonempty β]

/-- An almost-sure bound on conditional moments remains valid after restricting
the observation to any measurable event of positive probability. -/
theorem event_moment_le_of_slice_moments (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) {f : β → ℝ} (hi : Integrable f μ) (c : ℝ)
    (hc : ∀ᵐ x ∂μ.map X, (∫ z, f z ∂condDistrib id X μ x) ≤ c)
    (D : Set α) (hD : MeasurableSet D) (hpos : μ (X ⁻¹' D) ≠ 0) :
    (∫ z, f z ∂μ[|X ⁻¹' D]) ≤ c := by
  let m := MeasurableSpace.comap X (inferInstance : MeasurableSpace α)
  letI : MeasurableSpace β := mβ
  have hm : m ≤ mβ := hX.comap_le
  have hs : MeasurableSet[m] (X ⁻¹' D) := ⟨D, hD, rfl⟩
  have he := condExp_ae_eq_integral_condDistrib_id hX hi
  have hpull := ae_of_ae_map hX.aemeasurable hc
  have hbound : ∀ᵐ z ∂μ, (μ[f|m]) z ≤ c := by
    filter_upwards [he, hpull] with z hz hb
    rw [hz]
    exact hb
  have h : (∫ z in X ⁻¹' D, (μ[f|m]) z ∂μ) ≤ ∫ z in X ⁻¹' D, c ∂μ :=
    integral_mono_ae (integrable_condExp (μ := μ) (m := m) (f := f)).restrict
      (integrable_const c) (ae_restrict_of_ae hbound)
  rw [setIntegral_condExp hm hi hs, integral_const] at h
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at h
  have hp : 0 < μ.real (X ⁻¹' D) := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real (X ⁻¹' D))⁻¹ * (∫ z in X ⁻¹' D, f z ∂μ) ≤ c
  rw [← div_eq_inv_mul, div_le_iff₀ hp]
  exact h.trans_eq (mul_comm _ _)

end
end Nonsmooth
