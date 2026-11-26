import Nonsmooth.RankMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem rankPower_supported (n : ℕ) : ∀ᵐ p ∂rankPowerLaw n, p ∈ Ioo (0 : ℝ) 1 := by
  have hbase : ∀ᵐ p ∂(volume : Measure ℝ).restrict (Ioc 0 1), p ∈ Ioo (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc 0 1)]
    exact ae_restrict_mem measurableSet_Ioo
  exact (withDensity_absolutelyContinuous _ _).ae_le hbase

theorem tail_entropy_pointwise {p K : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hK : 0 < K) :
    ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p)) ≤
      Real.log K * ((1 - p) / p) ^ 2 + (1 / K) * ((1 - p) / p ^ 2) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have hlog : Real.log (1 / (1 - p)) ≤ Real.log K + 1 / (K * (1 - p)) := by
    calc
      _ = Real.log K + Real.log (1 / (K * (1 - p))) := by
        rw [← Real.log_mul hK.ne' (one_div_ne_zero (mul_ne_zero hK.ne' hq.ne'))]
        congr 1
        field_simp
      _ ≤ _ := by
        have hh := (Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (K * (1 - p)))).trans
          (sub_le_self _ zero_le_one)
        linarith only [hh]
  have h := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((1 - p) / p))
  have heq : ((1 - p) / p) ^ 2 * (Real.log K + 1 / (K * (1 - p))) =
      Real.log K * ((1 - p) / p) ^ 2 + (1 / K) * ((1 - p) / p ^ 2) := by
    field_simp [hp.1.ne', hq.ne', hK.ne'] <;> ring
  exact h.trans_eq heq

theorem tail_entropy_nonneg {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p)) := by
  apply mul_nonneg (sq_nonneg _)
  apply Real.log_nonneg
  exact (one_le_div (sub_pos.mpr hp.2)).mpr (by linarith [hp.1])

theorem rankPower_tail_entropy (m : ℕ) {K : ℝ} (hK : 0 < K) :
    Integrable (fun p : ℝ => ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p)))
      (rankPowerLaw (m + 2)) ∧
    (∫ p : ℝ, ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p)) ∂rankPowerLaw (m + 2)) ≤
      Real.log K * (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3))) +
        (1 / K) * (1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
  have hfirst := rankPower_inverse_tail_first m
  have hsecond := rankPower_inverse_tail_second m
  have hR : Integrable (fun p : ℝ => Real.log K * ((1 - p) / p) ^ 2 +
      (1 / K) * ((1 - p) / p ^ 2)) (rankPowerLaw (m + 2)) :=
    (hsecond.1.const_mul (Real.log K)).add (hfirst.1.const_mul (1 / K))
  have hle : (fun p : ℝ => ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p))) ≤ᵐ[rankPowerLaw (m + 2)]
      (fun p => Real.log K * ((1 - p) / p) ^ 2 + (1 / K) * ((1 - p) / p ^ 2)) := by
    filter_upwards [rankPower_supported (m + 2)] with p hp
    exact tail_entropy_pointwise hp hK
  have hm : Measurable (fun p : ℝ => ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p))) := by fun_prop
  have hi : Integrable (fun p : ℝ => ((1 - p) / p) ^ 2 * Real.log (1 / (1 - p)))
      (rankPowerLaw (m + 2)) := by
    apply hR.mono' hm.aestronglyMeasurable
    filter_upwards [rankPower_supported (m + 2), hle] with p hp hple
    simpa only [Real.norm_of_nonneg (tail_entropy_nonneg hp)] using hple
  refine ⟨hi, (integral_mono_ae hi hR hle).trans_eq ?_⟩
  rw [integral_add (hsecond.1.const_mul _) (hfirst.1.const_mul _),
    integral_const_mul, integral_const_mul, hsecond.2, hfirst.2]

end
end Nonsmooth
