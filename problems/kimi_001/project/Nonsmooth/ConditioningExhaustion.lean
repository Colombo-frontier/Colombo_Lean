import Nonsmooth.IntervalDensityLaw
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

/-- Conditioning on increasing events exhausting the space recovers every integrable moment. -/
theorem integral_conditioning_exhaustion_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : (⋃ n, A n) = univ) :
    Tendsto (fun n => ∫ x, f x ∂μ[|A n]) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hnum : Tendsto (fun n => ∫ x in A n, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone hA hmono hf.integrableOn
    simpa only [hcover, Measure.restrict_univ] using h
  have hmass : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (1 : ℝ)) := by
    have h := tendsto_setIntegral_of_monotone hA hmono (integrable_const (1 : ℝ) (μ := μ)).integrableOn
    simpa only [hcover, Measure.restrict_univ, integral_const, measureReal_univ_eq_one,
      smul_eq_mul, mul_one, Measure.restrict_apply_univ, measureReal_def, measure_univ,
      ENNReal.toReal_one] using h
  have h := hnum.div hmass (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  funext n
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

theorem variance_conditioning_exhaustion_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : (⋃ n, A n) = univ) (hpos : ∀ n, μ (A n) ≠ 0) :
    Tendsto (fun n => variance f μ[|A n]) atTop (𝓝 (variance f μ)) := by
  have h1 := integral_conditioning_exhaustion_tendsto μ (hf.integrable (by norm_num)) A hA hmono hcover
  have h2 := integral_conditioning_exhaustion_tendsto μ hf.integrable_sq A hA hmono hcover
  have hν (n : ℕ) : MemLp f 2 μ[|A n] :=
    (hf.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr (hpos n))
  have he (n : ℕ) : variance f μ[|A n] =
      (∫ x, f x ^ 2 ∂μ[|A n]) - (∫ x, f x ∂μ[|A n]) ^ 2 := by
    letI : IsProbabilityMeasure μ[|A n] := cond_isProbabilityMeasure (hpos n)
    simpa only [Pi.pow_apply] using variance_eq_sub (hν n)
  rw [variance_eq_sub hf]
  convert! h2.sub (h1.pow 2) using 1
  exact funext he

/-- Uniform conditional variance bounds pass to the complete distribution by exhaustion. -/
theorem variance_le_of_conditioning_exhaustion (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : (⋃ n, A n) = univ) (hpos : ∀ n, μ (A n) ≠ 0)
    {C : ℝ} (hbound : ∀ n, variance f μ[|A n] ≤ C) : variance f μ ≤ C :=
  le_of_tendsto (variance_conditioning_exhaustion_tendsto μ hf A hA hmono hcover hpos)
    (Eventually.of_forall hbound)

end
end Nonsmooth
