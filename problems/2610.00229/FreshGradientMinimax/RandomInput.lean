import FreshGradientMinimax.KernelIteration

/-! Integrating a pointwise kernel moment bound over arbitrary random input. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem kernel_moment_from_envelope (K : Kernel X Y) [IsMarkovKernel K]
    (ν : Measure X) [IsProbabilityMeasure ν] (V : Y → ℝ) (hV : StronglyMeasurable V)
    (hpos : ∀ y, 0 ≤ V y) (W : X → ℝ) (hW : Integrable W ν)
    (hi : ∀ x, Integrable V (K x)) (hbound : ∀ x, (∫ y, V y ∂K x) ≤ W x) :
    Integrable V (K ∘ₘ ν) ∧ (∫ y, V y ∂K ∘ₘ ν) ≤ ∫ x, W x ∂ν := by
  have hmean : Integrable (fun x => ∫ y, V y ∂K x) ν := by
    apply hW.mono' hV.integral_kernel.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hpos)]
      exact hbound x)
  have hInt : Integrable V ((K ∘ₖ Kernel.const Unit ν) ()) := by
    apply (ProbabilityTheory.integrable_comp_iff hV.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    simpa only [Kernel.const_apply, Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hmean
  rw [Measure.comp_eq_comp_const_apply]
  refine ⟨hInt, ?_⟩
  rw [Kernel.integral_comp hInt, Kernel.const_apply]
  exact integral_mono hmean hW hbound

end FreshGradientMinimax
