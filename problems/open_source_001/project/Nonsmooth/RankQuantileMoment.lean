import Nonsmooth.RankMoments

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def rankQuantileLog (p : ℝ) : ℝ := Real.log (1 / min p (1 - p))

theorem unit_interval_inverse_sqrt_moment :
    Integrable (fun p : ℝ => p ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      (∫ p in Ioc (0 : ℝ) 1, p ^ (-(1 / 2 : ℝ))) = 2 := by
  refine ⟨(intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1, ?_⟩
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num

theorem unit_interval_reflected_inverse_sqrt_moment :
    Integrable (fun p : ℝ => (1 - p) ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      (∫ p in Ioc (0 : ℝ) 1, (1 - p) ^ (-(1 / 2 : ℝ))) = 2 := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left 1
  have hi' : IntervalIntegrable (fun p : ℝ => (1 - p) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using hi.symm
  refine ⟨hi'.1, ?_⟩
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1]
  simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    unit_interval_inverse_sqrt_moment.2

theorem rankQuantile_exponential_moment :
    Integrable (fun p => Real.exp (rankQuantileLog p / 2)) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      (∫ p in Ioc (0 : ℝ) 1, Real.exp (rankQuantileLog p / 2)) ≤ 4 := by
  have hsupport : ∀ᵐ p ∂(volume : Measure ℝ).restrict (Ioc 0 1), p ∈ Ioo (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc 0 1)]
    exact ae_restrict_mem measurableSet_Ioo
  have he (z : ℝ) (hz : 0 < z) : Real.exp (Real.log (1 / z) / 2) = z ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, Real.log_inv, Real.rpow_def_of_pos hz]
    congr 1
    ring
  have hbound : ∀ᵐ p ∂(volume : Measure ℝ).restrict (Ioc 0 1),
      Real.exp (rankQuantileLog p / 2) ≤ p ^ (-(1 / 2 : ℝ)) + (1 - p) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [hsupport] with p hp
    dsimp only [rankQuantileLog]
    rcases le_total p (1 - p) with h | h
    · rw [min_eq_left h, he p hp.1]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [hp.2]) _)
    · rw [min_eq_right h, he (1 - p) (by linarith [hp.2])]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hp.1.le _)
  have hsum := unit_interval_inverse_sqrt_moment.1.add unit_interval_reflected_inverse_sqrt_moment.1
  have hm : Measurable (fun p => Real.exp (rankQuantileLog p / 2)) := by
    unfold rankQuantileLog
    fun_prop
  have hi : Integrable (fun p => Real.exp (rankQuantileLog p / 2)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply hsum.mono' hm.aestronglyMeasurable
    filter_upwards [hbound] with p hp
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le, Pi.add_apply] using hp
  refine ⟨hi, (integral_mono_ae hi hsum hbound).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add unit_interval_inverse_sqrt_moment.1 unit_interval_reflected_inverse_sqrt_moment.1,
    unit_interval_inverse_sqrt_moment.2, unit_interval_reflected_inverse_sqrt_moment.2]
  norm_num

/-- A distribution-free exponential moment for the smaller CDF tail rank. -/
theorem atomless_cdf_quantile_exponential_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) :
    Integrable (fun x => Real.exp (rankQuantileLog (cdf μ x) / 2)) μ ∧
      (∫ x, Real.exp (rankQuantileLog (cdf μ x) / 2) ∂μ) ≤ 4 := by
  have hc := (continuous_cdf_of_atomless μ hμ).measurable
  have hf : Measurable (fun p => Real.exp (rankQuantileLog p / 2)) := by
    unfold rankQuantileLog
    fun_prop
  have hm := atomless_cdf_map_uniform μ hμ
  have hi := rankQuantile_exponential_moment.1
  have hb := rankQuantile_exponential_moment.2
  rw [← hm] at hi hb
  exact ⟨(integrable_map_measure hf.aestronglyMeasurable hc.aemeasurable).mp hi,
    by simpa only [integral_map_of_stronglyMeasurable hc hf.stronglyMeasurable] using hb⟩

end
end Nonsmooth
