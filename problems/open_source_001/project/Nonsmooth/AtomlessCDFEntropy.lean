import Nonsmooth.RankQuantileMoment

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem unit_interval_log_inverse_moment :
    Integrable (fun p : ℝ => Real.log (1 / p)) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      (∫ p in Ioc (0 : ℝ) 1, Real.log (1 / p)) = 1 := by
  have hi : Integrable (fun p : ℝ => -Real.log p) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).1.neg
    unfold IntegrableOn at h
    exact h.congr (Eventually.of_forall (fun p => rfl))
  refine ⟨by simpa only [one_div, Real.log_inv, Pi.neg_apply] using hi, ?_⟩
  simp_rw [one_div, Real.log_inv]
  rw [integral_neg, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_log]
  norm_num

theorem atomless_cdf_interior_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) : ∀ᵐ x ∂μ, cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  have hp : ∀ᵐ p ∂μ.map (cdf μ), p ∈ Ioo (0 : ℝ) 1 := by
    rw [atomless_cdf_map_uniform μ hμ,
      ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc 0 1)]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_of_ae_map (continuous_cdf_of_atomless μ hμ).measurable.aemeasurable hp

/-- The lower-tail information of an atomless observation has expectation exactly one. -/
theorem atomless_cdf_log_inverse_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) :
    Integrable (fun x => Real.log (1 / cdf μ x)) μ ∧
      (∫ x, Real.log (1 / cdf μ x) ∂μ) = 1 := by
  have hc := (continuous_cdf_of_atomless μ hμ).measurable
  have hf : Measurable (fun p : ℝ => Real.log (1 / p)) := by fun_prop
  have hi := unit_interval_log_inverse_moment.1
  have he := unit_interval_log_inverse_moment.2
  rw [← atomless_cdf_map_uniform μ hμ] at hi he
  exact ⟨(integrable_map_measure hf.aestronglyMeasurable hc.aemeasurable).mp hi,
    by simpa only [integral_map_of_stronglyMeasurable hc hf.stronglyMeasurable] using he⟩

end
end Nonsmooth
