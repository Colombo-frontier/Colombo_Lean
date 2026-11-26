import Nonsmooth.WeightedDensityLaw
import Nonsmooth.GaussianEventSlices

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem withDensity_product_fst (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (w : α × β → ℝ≥0∞) (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.fst =
      μ.withDensity (fun t => ∫⁻ x, w (t, x) ∂ν) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA,
    withDensity_apply _ (hA.preimage measurable_fst), withDensity_apply _ hA,
    ← lintegral_indicator (hA.preimage measurable_fst), ← lintegral_indicator hA,
    lintegral_prod _ (hw.indicator (hA.preimage measurable_fst)).aemeasurable]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ A
  · simp only [Set.indicator_of_mem ht]
    apply lintegral_congr
    intro x
    exact Set.indicator_of_mem (show (t, x) ∈ Prod.fst ⁻¹' A from ht) w
  · simp only [Set.indicator_of_notMem ht]
    simpa only [lintegral_zero] using lintegral_congr (fun x => Set.indicator_of_notMem
      (show (t, x) ∉ Prod.fst ⁻¹' A from ht) w)

/-- Fubini identifies the actual normalized marginal of a positive
product density, including its normalizing constant. -/
theorem weightedDensityLaw_product_marginal (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (w : α × β → ℝ) (hw : Measurable w) (hw0 : ∀ p, 0 ≤ w p)
    (hi : ∀ t, Integrable (fun x => w (t, x)) ν) :
    (weightedDensityLaw (μ.prod ν) w).map Prod.fst =
      weightedDensityLaw μ (fun t => ∫ x, w (t, x) ∂ν) := by
  have hmass (t : α) : (∫⁻ x, ENNReal.ofReal (w (t, x)) ∂ν) = ENNReal.ofReal (∫ x, w (t, x) ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal (hi t) (Eventually.of_forall (fun x => hw0 (t, x)))).symm
  have hraw := withDensity_product_fst μ ν (fun p => ENNReal.ofReal (w p)) hw.ennreal_ofReal
  simp_rw [hmass] at hraw
  have hcond := conditioning_map_preimage ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (w p)))
    Prod.fst measurable_fst univ MeasurableSet.univ
  simpa only [Set.preimage_univ, weightedDensityLaw, hraw] using hcond.symm

end
end Nonsmooth
