import Nonsmooth.FiniteProductKernel

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem parametric_conditioning_measurable (μ : Measure β) [IsProbabilityMeasure μ]
    {B : Set (α × β)} (hB : MeasurableSet B) :
    Measurable (fun x : α => μ[|Prod.mk x ⁻¹' B]) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have h1 : Measurable (fun x : α => μ (Prod.mk x ⁻¹' B)) := measurable_measure_prodMk_left hB
  have h2 : Measurable (fun x : α => μ ((Prod.mk x ⁻¹' B) ∩ s)) :=
    measurable_measure_prodMk_left (hB.inter (measurable_snd hs))
  have he (x : α) : μ[|Prod.mk x ⁻¹' B] s = (μ (Prod.mk x ⁻¹' B))⁻¹ * μ ((Prod.mk x ⁻¹' B) ∩ s) :=
    cond_apply (measurable_prodMk_left hB) μ s
  simp_rw [he]
  exact h1.inv.mul h2

/-- Event conditioning as a Markov kernel, with the original law chosen at zero-mass parameters. -/
def parametricEventKernel (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) : Kernel α β where
  toFun x := if μ (Prod.mk x ⁻¹' B) = 0 then μ else μ[|Prod.mk x ⁻¹' B]
  measurable' := by
    have hmass : Measurable (fun x : α => μ (Prod.mk x ⁻¹' B)) := measurable_measure_prodMk_left hB
    exact Measurable.ite (hmass (measurableSet_singleton 0)) measurable_const
      (parametric_conditioning_measurable μ hB)

theorem parametricEventKernel_apply (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) (x : α) (hx : μ (Prod.mk x ⁻¹' B) ≠ 0) :
    parametricEventKernel μ B hB x = μ[|Prod.mk x ⁻¹' B] := by
  change (if μ (Prod.mk x ⁻¹' B) = 0 then μ else μ[|Prod.mk x ⁻¹' B]) = _
  rw [if_neg hx]

instance parametricEventKernel_markov (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) : IsMarkovKernel (parametricEventKernel μ B hB) where
  isProbabilityMeasure x := by
    by_cases hx : μ (Prod.mk x ⁻¹' B) = 0
    · change IsProbabilityMeasure (if μ (Prod.mk x ⁻¹' B) = 0 then μ else μ[|Prod.mk x ⁻¹' B])
      rw [if_pos hx]
      infer_instance
    · rw [parametricEventKernel_apply μ B hB x hx]
      exact cond_isProbabilityMeasure hx

theorem parametricEventKernel_weighted_apply (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) (x : α) (s : Set β) :
    μ (Prod.mk x ⁻¹' B) * parametricEventKernel μ B hB x s = μ ((Prod.mk x ⁻¹' B) ∩ s) := by
  by_cases hx : μ (Prod.mk x ⁻¹' B) = 0
  · rw [hx, zero_mul, measure_mono_null inter_subset_left hx]
  · rw [parametricEventKernel_apply μ B hB x hx, cond_apply (measurable_prodMk_left hB),
      ← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]

theorem parametricEventKernel_weighted_measure (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) (x : α) :
    μ (Prod.mk x ⁻¹' B) • parametricEventKernel μ B hB x = μ.restrict (Prod.mk x ⁻¹' B) := by
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, parametricEventKernel_weighted_apply,
    Measure.restrict_apply hs, inter_comm]

theorem parametricEventKernel_weighted_lintegral (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) (x : α) (f : β → ℝ≥0∞) :
    μ (Prod.mk x ⁻¹' B) * (∫⁻ z, f z ∂parametricEventKernel μ B hB x) =
      ∫⁻ z in Prod.mk x ⁻¹' B, f z ∂μ := by
  have h := congrArg (fun ν : Measure β => ∫⁻ z, f z ∂ν)
    (parametricEventKernel_weighted_measure μ B hB x)
  simpa only [lintegral_smul_measure, smul_eq_mul] using h

/-- The normalized event kernels recover every nonnegative integral on the original joint event. -/
theorem parametricEventKernel_joint_lintegral (σ : Measure α) [SFinite σ]
    (μ : Measure β) [IsProbabilityMeasure μ] (B : Set (α × β)) (hB : MeasurableSet B)
    (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, μ (Prod.mk x ⁻¹' B) * (∫⁻ z, f (x, z) ∂parametricEventKernel μ B hB x) ∂σ) =
      ∫⁻ q in B, f q ∂σ.prod μ := by
  simp_rw [parametricEventKernel_weighted_lintegral]
  rw [← lintegral_indicator hB, lintegral_prod _ (hf.indicator hB).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← lintegral_indicator (measurable_prodMk_left hB)]
  apply lintegral_congr
  intro z
  by_cases hz : (x, z) ∈ B
  · simp [hz]
  · simp [hz]

end
end Nonsmooth
