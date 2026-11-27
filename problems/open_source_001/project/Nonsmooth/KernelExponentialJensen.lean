import Nonsmooth.PotentialJointDensity
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem kernel_mean_integrable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (f : α × β → ℝ) (hf : Measurable f) (hi : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun a => ∫ b, f (a, b) ∂κ a) μ := by
  have hn := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).2
  apply hn.mono' hf.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
  exact Eventually.of_forall (fun a => norm_integral_le_integral_norm _)

/-- Conditional Jensen proved for the actual kernel integrals, with exponential
integrability inherited from the joint law. -/
theorem kernel_exponential_jensen {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (f : α × β → ℝ) (hf : Measurable f) (hi : Integrable f (μ ⊗ₘ κ))
    (he : Integrable (fun p => Real.exp (f p)) (μ ⊗ₘ κ)) :
    Integrable (fun a => Real.exp (∫ b, f (a, b) ∂κ a)) μ ∧
      (∫ a, Real.exp (∫ b, f (a, b) ∂κ a) ∂μ) ≤ ∫ p, Real.exp (f p) ∂(μ ⊗ₘ κ) := by
  have hfi := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).1
  have hei := ((Measure.integrable_compProd_iff he.aestronglyMeasurable).mp he).1
  have hJ : ∀ᵐ a ∂μ, Real.exp (∫ b, f (a, b) ∂κ a) ≤ ∫ b, Real.exp (f (a, b)) ∂κ a := by
    filter_upwards [hfi, hei] with a hfa hea
    exact (convexOn_exp : ConvexOn ℝ univ Real.exp).map_integral_le
      Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun _ => mem_univ _)) hfa hea
  have houter := kernel_mean_integrable μ κ (fun p => Real.exp (f p))
    (Real.continuous_exp.measurable.comp hf) he
  have hmean := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  have hleft : Integrable (fun a => Real.exp (∫ b, f (a, b) ∂κ a)) μ := by
    apply houter.mono' (Real.continuous_exp.comp_aestronglyMeasurable hmean.aestronglyMeasurable)
    filter_upwards [hJ] with a ha
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using ha
  refine ⟨hleft, ?_⟩
  rw [Measure.integral_compProd he]
  exact integral_mono_ae hleft houter hJ

end
end Nonsmooth
