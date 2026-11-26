import Nonsmooth.SupportPosteriorKernel

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {β : Type} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

/-- Restricting the original law and then projecting weights the projected law by the slice probability. -/
theorem projection_slice_restrict_map (μ : Measure β) [IsProbabilityMeasure μ]
    (r : β → ℝ) (hr : Measurable r) {A : Set β} (hA : MeasurableSet A) :
    (μ.restrict A).map r = (μ.map r).withDensity (fun y => condDistrib id r μ y A) := by
  ext D hD
  rw [Measure.map_apply hr hD, Measure.restrict_apply (hr hD), withDensity_apply _ hD,
    setLIntegral_map hD (Kernel.measurable_coe _ hA) hr,
    setLIntegral_preimage_condDistrib hr aemeasurable_id hA hD]
  rfl

theorem projection_slice_weighted_integral (μ : Measure β) [IsProbabilityMeasure μ]
    (r : β → ℝ) (hr : Measurable r) {A : Set β} (hA : MeasurableSet A)
    {D : Set ℝ} (hD : MeasurableSet D) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in A ∩ r ⁻¹' D, g (r z) ∂μ) =
      ∫⁻ y in D, g y * condDistrib id r μ y A ∂μ.map r := by
  have h := congrArg (fun ν : Measure ℝ => ∫⁻ y in D, g y ∂ν)
    (projection_slice_restrict_map μ r hr hA)
  rw [setLIntegral_map hD hg hr, Measure.restrict_restrict (hr hD),
    setLIntegral_withDensity_eq_setLIntegral_mul _ (Kernel.measurable_coe _ hA) hg hD] at h
  simpa only [inter_comm, Pi.mul_apply, mul_comm] using h

end
end Nonsmooth
