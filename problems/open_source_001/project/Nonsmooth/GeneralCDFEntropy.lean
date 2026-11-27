import Nonsmooth.GeneralCDFRank
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem cdf_log_inverse_nonneg (μ : Measure ℝ) (y : ℝ) :
    0 ≤ Real.log (1 / cdf μ y) := by
  by_cases h0 : cdf μ y = 0
  · simp [h0]
  have hp : 0 < cdf μ y := lt_of_le_of_ne (cdf_nonneg μ y) (Ne.symm h0)
  exact Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using cdf_le_one μ y))

theorem cdf_log_inverse_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {y : ℝ | t < Real.log (1 / cdf μ y)} ≤ Real.exp (-t) := by
  have hs : {y : ℝ | t < Real.log (1 / cdf μ y)} ⊆
      {y : ℝ | cdf μ y ≤ Real.exp (-t)} := by
    intro y hy
    change t < Real.log (1 / cdf μ y) at hy
    change cdf μ y ≤ Real.exp (-t)
    by_cases h0 : cdf μ y = 0
    · rw [h0]
      exact (Real.exp_pos _).le
    have hp : 0 < cdf μ y := lt_of_le_of_ne (cdf_nonneg μ y) (Ne.symm h0)
    rw [one_div, Real.log_inv] at hy
    have hlog : Real.log (cdf μ y) < -t := by linarith
    have he := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log hp] at he
    exact he.le
  exact (measureReal_mono hs).trans (cdf_rank_probability_le μ (Real.exp_pos _).le)

/-- The expected lower-tail information is at most one for every real
probability law, including laws with atoms. -/
theorem cdf_log_inverse_moment_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun y : ℝ => Real.log (1 / cdf μ y)) μ ∧
      (∫ y : ℝ, Real.log (1 / cdf μ y) ∂μ) ≤ 1 := by
  let f : ℝ → ℝ := fun y => Real.log (1 / cdf μ y)
  have hf : Measurable f := by
    exact (((monotone_cdf μ).measurable.const_div 1).log)
  have hn : 0 ≤ᵐ[μ] f := Eventually.of_forall (cdf_log_inverse_nonneg μ)
  have hExp : (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
      (Eventually.of_forall (fun t => (Real.exp_pos (-t)).le)), integral_exp_neg_Ioi_zero]
    norm_num
  have hlin : (∫⁻ y, ENNReal.ofReal (f y) ∂μ) ≤ 1 := by
    rw [lintegral_eq_lintegral_meas_lt μ hn hf.aemeasurable, ← hExp]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    have htail := cdf_log_inverse_tail μ ht.le
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {y : ℝ | t < f y})]
    exact ENNReal.ofReal_le_ofReal htail
  have hi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hn).mp
      (ne_of_lt (hlin.trans_lt (by simp)))
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hf.aestronglyMeasurable]
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) hlin

end
end Nonsmooth
