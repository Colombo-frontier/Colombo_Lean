import Nonsmooth.GaussianIntervalMGF

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

theorem integral_conditioning_ae_exhaustion_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n) :
    Tendsto (fun n => ∫ x, f x ∂μ[|A n]) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hrestrict : μ.restrict (⋃ n, A n) = μ := Measure.restrict_eq_self_of_ae_mem hcover
  have hnum : Tendsto (fun n => ∫ x in A n, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone hA hmono hf.integrableOn
    simpa only [hrestrict] using h
  have hmass : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (1 : ℝ)) := by
    have h := tendsto_setIntegral_of_monotone hA hmono (integrable_const (1 : ℝ) (μ := μ)).integrableOn
    simpa only [hrestrict, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one,
      Measure.restrict_apply_univ, measureReal_def, measure_univ, ENNReal.toReal_one] using h
  have h := hnum.div hmass (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  funext n
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

theorem variance_conditioning_ae_exhaustion_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n) (hpos : ∀ n, μ (A n) ≠ 0) :
    Tendsto (fun n => variance f μ[|A n]) atTop (𝓝 (variance f μ)) := by
  have h1 := integral_conditioning_ae_exhaustion_tendsto μ (hf.integrable (by norm_num)) A hA hmono hcover
  have h2 := integral_conditioning_ae_exhaustion_tendsto μ hf.integrable_sq A hA hmono hcover
  have hν (n : ℕ) : MemLp f 2 μ[|A n] :=
    (hf.mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr (hpos n))
  have he (n : ℕ) : variance f μ[|A n] =
      (∫ x, f x ^ 2 ∂μ[|A n]) - (∫ x, f x ∂μ[|A n]) ^ 2 := by
    letI : IsProbabilityMeasure μ[|A n] := cond_isProbabilityMeasure (hpos n)
    exact variance_eq_sub (hν n)
  rw [variance_eq_sub hf]
  simp only [Pi.pow_apply]
  convert! h2.sub (h1.pow 2) using 1
  exact funext he

theorem variance_le_of_ae_conditioning_exhaustion (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n) (hpos : ∀ n, μ (A n) ≠ 0)
    {C : ℝ} (hbound : ∀ n, variance f μ[|A n] ≤ C) : variance f μ ≤ C :=
  le_of_tendsto (variance_conditioning_ae_exhaustion_tendsto μ hf A hA hmono hcover hpos)
    (Eventually.of_forall hbound)

theorem centered_exp_integral_factor (μ : Measure α) (f : α → ℝ) (t m : ℝ) :
    (∫ x, Real.exp (t * (f x - m)) ∂μ) = Real.exp (-t * m) * ∫ x, Real.exp (t * f x) ∂μ := by
  have he : (fun x => Real.exp (t * (f x - m))) = fun x => Real.exp (-t * m) * Real.exp (t * f x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul]

/-- Centered exponential-moment estimates pass through increasing conditioning events
covering almost every point, with the conditional centers allowed to vary. -/
theorem centered_mgf_le_of_ae_conditioning_exhaustion (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (t : ℝ) (hExp : Integrable (fun x => Real.exp (t * f x)) μ)
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n) {C : ℝ}
    (hbound : ∀ n, (∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ[|A n])) ∂μ[|A n]) ≤ C) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ) ≤ C := by
  have hmean := integral_conditioning_ae_exhaustion_tendsto μ hf A hA hmono hcover
  have hexp := integral_conditioning_ae_exhaustion_tendsto μ hExp A hA hmono hcover
  have hscale : Tendsto (fun n => Real.exp (-t * ∫ y, f y ∂μ[|A n])) atTop
      (𝓝 (Real.exp (-t * ∫ y, f y ∂μ))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul hmean)
  have hlim := hscale.mul hexp
  rw [centered_exp_integral_factor]
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  rw [← centered_exp_integral_factor]
  exact hbound n

end
end Nonsmooth
