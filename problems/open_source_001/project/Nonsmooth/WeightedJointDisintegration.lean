import Nonsmooth.WeightedPosteriorKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem map_withDensity_comp (μ : Measure α) (X : α → β) (hX : Measurable X)
    (w : β → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (X x))).map X = (μ.map X).withDensity w := by
  ext S hS
  rw [Measure.map_apply hX hS, withDensity_apply _ (hX hS), withDensity_apply _ hS,
    setLIntegral_map hS hw hX]

theorem kernel_weight_density_finite (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (w : β → ℝ) (hb : ∀ z, w z ≤ 1) :
    IsFiniteMeasure (ν.withDensity (kernelWeightMass κ w)) := by
  apply isFiniteMeasure_of_le ν
  calc
    _ ≤ ν.withDensity (fun _ => 1) := withDensity_mono
      (Eventually.of_forall (kernelWeightMass_le_one κ w hb))
    _ = ν := by simp

/-- Exact reweighting of a joint law and its conditional kernel, including
parameters with zero local weight. -/
theorem weightedPosteriorKernel_disintegration (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (w : β → ℝ) (hw : Measurable w)
    (hb : ∀ z, w z ≤ 1) :
    (ν ⊗ₘ κ).withDensity (fun p : α × β => ENNReal.ofReal (w p.2)) =
      (ν.withDensity (kernelWeightMass κ w)) ⊗ₘ weightedPosteriorKernel κ w hw := by
  letI := weightedPosteriorKernel_markov κ w hw hb
  letI := kernel_weight_density_finite ν κ w hb
  ext S hS
  have hg : Measurable (fun p : α × β => ENNReal.ofReal (w p.2)) :=
    hw.ennreal_ofReal.comp measurable_snd
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    Measure.lintegral_compProd (hg.indicator hS),
    Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul _ (kernelWeightMass_measurable κ w hw)
      (Kernel.measurable_kernel_prodMk_left hS)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [weightedPosteriorKernel_weighted_apply κ w hw hb,
    withDensity_apply _ (measurable_prodMk_left hS), ← lintegral_indicator (measurable_prodMk_left hS)]
  rfl

end
end Nonsmooth
