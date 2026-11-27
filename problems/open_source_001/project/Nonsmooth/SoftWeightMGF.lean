import Nonsmooth.SoftWeightLimits
import Nonsmooth.ConditioningAEExhaustion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

theorem soft_weighted_centered_exp_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (t : ℝ) (hExp : Integrable (fun x => Real.exp (t * f x)) μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) :
    Tendsto (fun n => ∫ x, Real.exp (t * (f x - ∫ z, f z ∂weightedDensityLaw μ (w n)))
      ∂weightedDensityLaw μ (w n)) atTop (𝓝 (∫ x, Real.exp (t * (f x - ∫ z, f z ∂μ[|A])) ∂μ[|A])) := by
  have hm := soft_weighted_law_integral_tendsto μ f hf w hw hb A hA hpos hlim
  have he := soft_weighted_law_integral_tendsto μ _ hExp w hw hb A hA hpos hlim
  have hs0 : Tendsto (fun n => -t * ∫ z, f z ∂weightedDensityLaw μ (w n)) atTop
      (𝓝 (-t * ∫ z, f z ∂μ[|A])) := tendsto_const_nhds.mul hm
  have hs : Tendsto (fun n => Real.exp (-t * ∫ z, f z ∂weightedDensityLaw μ (w n))) atTop
      (𝓝 (Real.exp (-t * ∫ z, f z ∂μ[|A]))) := (Real.continuous_exp.tendsto _).comp hs0
  simpa only [centered_exp_integral_factor] using hs.mul he

/-- Centered MGF bounds pass from positive soft-weight laws to the hard
event-conditioned law with its actual changing center. -/
theorem soft_weighted_centered_mgf_bound (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (t : ℝ) (hExp : Integrable (fun x => Real.exp (t * f x)) μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)))
    (C : ℝ) (hbound : ∀ n, (∫ x, Real.exp (t * (f x - ∫ z, f z ∂weightedDensityLaw μ (w n)))
      ∂weightedDensityLaw μ (w n)) ≤ C) :
    Integrable (fun x => Real.exp (t * (f x - ∫ z, f z ∂μ[|A]))) μ[|A] ∧
      (∫ x, Real.exp (t * (f x - ∫ z, f z ∂μ[|A])) ∂μ[|A]) ≤ C := by
  have heA : Integrable (fun x => Real.exp (t * f x)) μ[|A] :=
    (hExp.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have heq : (fun x => Real.exp (t * (f x - ∫ z, f z ∂μ[|A]))) =
      (fun x => Real.exp (-t * ∫ z, f z ∂μ[|A]) * Real.exp (t * f x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, le_of_tendsto (soft_weighted_centered_exp_tendsto μ f hf t hExp w hw hb A hA hpos hlim)
    (Eventually.of_forall hbound)⟩
  rw [heq]
  exact heA.const_mul _

end
end Nonsmooth
