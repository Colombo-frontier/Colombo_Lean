import Nonsmooth.SoftProjectionLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

theorem memLp_two_unit_weightedLaw (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ)
    (w : α → ℝ) (hw : Measurable w) (hb : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    MemLp f 2 (weightedDensityLaw μ w) := by
  apply (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr
  exact integrable_unit_weightedLaw μ (fun x => f x ^ 2) hf.integrable_sq w hw hb

theorem soft_weighted_variance_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 < w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) :
    Tendsto (fun n => variance f (weightedDensityLaw μ (w n))) atTop
      (𝓝 (variance f μ[|A])) := by
  have hb' (n : ℕ) (x : α) : 0 ≤ w n x ∧ w n x ≤ 1 := ⟨(hb n x).1.le, (hb n x).2⟩
  have h1 := soft_weighted_law_integral_tendsto μ f (hf.integrable (by norm_num))
    w hw hb' A hA hpos hlim
  have h2 := soft_weighted_law_integral_tendsto μ (fun x => f x ^ 2) hf.integrable_sq
    w hw hb' A hA hpos hlim
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
  have hA2 : MemLp f 2 μ[|A] :=
    (hf.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have he (n : ℕ) : variance f (weightedDensityLaw μ (w n)) =
      (∫ x, f x ^ 2 ∂weightedDensityLaw μ (w n)) -
        (∫ x, f x ∂weightedDensityLaw μ (w n)) ^ 2 := by
    letI : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
      weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb' n)
        (Eventually.of_forall (fun x => (hb n x).1))
    exact variance_eq_sub (memLp_two_unit_weightedLaw μ f hfm hf (w n) (hw n) (hb' n))
  rw [variance_eq_sub hA2]
  simp only [Pi.pow_apply]
  convert! h2.sub (h1.pow 2) using 1
  exact funext he

theorem conditioned_variance_le_of_soft_weights (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ)
    (w : ℕ → α → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n x, 0 < w n x ∧ w n x ≤ 1)
    (A : Set α) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)))
    {C : ℝ} (hbound : ∀ n, variance f (weightedDensityLaw μ (w n)) ≤ C) :
    variance f μ[|A] ≤ C :=
  le_of_tendsto (soft_weighted_variance_tendsto μ f hfm hf w hw hb A hA hpos hlim)
    (Eventually.of_forall hbound)

end
end Nonsmooth
