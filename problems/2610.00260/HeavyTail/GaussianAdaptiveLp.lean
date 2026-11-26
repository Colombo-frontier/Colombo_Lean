import HeavyTail.GaussianAdaptiveMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual Gaussian oracle noise belongs to Lp for every exponent at most two. -/

open MeasureTheory ProbabilityTheory
namespace HeavyTail.GaussianLower
noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace X]

theorem gaussianResponseKernel_noise_memLp (mean : X → E) (hm : Measurable mean)
    (σ : ℝ) {p : ℝ} (hp2 : p ≤ 2) (x : X) :
    MemLp (fun y ↦ y - ∫ z, z ∂gaussianResponseKernel mean hm σ x)
      (ENNReal.ofReal p) (gaussianResponseKernel mean hm σ x) := by
  rw [gaussianResponseKernel_unbiased]
  have hnoise : StronglyMeasurable (fun y : E ↦ y - mean x) :=
    (continuous_id.sub continuous_const).stronglyMeasurable
  have htwo : MemLp (fun y : E ↦ y - mean x) 2 (gaussianResponseKernel mean hm σ x) := by
    apply (memLp_two_iff_integrable_sq_norm hnoise.aestronglyMeasurable).mpr
    unfold gaussianResponseKernel
    rw [kernelOfSampler_apply]
    have hF : Measurable (fun z : E ↦ mean x + σ • z) := by fun_prop
    have hsq : StronglyMeasurable (fun y : E ↦ ‖y - mean x‖ ^ 2) :=
      hnoise.norm.pow 2
    apply (integrable_map_measure hsq.aestronglyMeasurable hF.aemeasurable).mpr
    simpa only [Function.comp_def, add_sub_cancel_left] using
      scaled_gaussian_second_integrable E σ
  exact htwo.mono_exponent (by exact_mod_cast ENNReal.ofReal_le_ofReal hp2)

end
end HeavyTail.GaussianLower
