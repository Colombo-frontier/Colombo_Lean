import Nonsmooth.SoftWeightCDF

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def softInequalityStep (n : ℕ) (t : ℝ) : ℝ := 1 / (1 + (Real.exp t) ^ n)

theorem softInequalityStep_pos (n : ℕ) (t : ℝ) : 0 < softInequalityStep n t := by
  unfold softInequalityStep
  positivity

theorem softInequalityStep_le_one (n : ℕ) (t : ℝ) : softInequalityStep n t ≤ 1 := by
  unfold softInequalityStep
  apply (div_le_iff₀ (by positivity : 0 < 1 + (Real.exp t) ^ n)).mpr
  nlinarith [pow_nonneg (Real.exp_pos t).le n]

theorem softInequalityStep_contDiff (n : ℕ) : ContDiff ℝ ⊤ (softInequalityStep n) := by
  exact contDiff_const.div (contDiff_const.add (Real.contDiff_exp.pow n)) (fun t => by positivity)

theorem softInequalityStep_tendsto_of_neg {t : ℝ} (ht : t < 0) :
    Tendsto (fun n => softInequalityStep n t) atTop (𝓝 (1 : ℝ)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos t).le (Real.exp_lt_one_iff.mpr ht)
  have hden : Tendsto (fun n => 1 + (Real.exp t) ^ n) atTop (𝓝 (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add hp
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div hden (by norm_num : (1 + 0 : ℝ) ≠ 0)
  convert! h using 1 <;> simp only [softInequalityStep, add_zero, div_one]

theorem softInequalityStep_tendsto_of_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => softInequalityStep n t) atTop (𝓝 (0 : ℝ)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-t)).le
    (Real.exp_lt_one_iff.mpr (by linarith : -t < 0))
  have he (n : ℕ) : softInequalityStep n t = (Real.exp (-t)) ^ n / (1 + (Real.exp (-t)) ^ n) := by
    rw [softInequalityStep, Real.exp_neg, inv_pow]
    have hn : (Real.exp t) ^ n ≠ 0 := pow_ne_zero n (Real.exp_ne_zero t)
    apply (div_eq_div_iff (by positivity : 1 + (Real.exp t) ^ n ≠ 0)
      (by positivity : 1 + ((Real.exp t) ^ n)⁻¹ ≠ 0)).mpr
    field_simp
    ring
  simp_rw [he]
  have hden : Tendsto (fun n => 1 + (Real.exp (-t)) ^ n) atTop (𝓝 (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add hp
  convert! hp.div hden (by norm_num : (1 + 0 : ℝ) ≠ 0) using 1 <;> simp only [add_zero, zero_div]

end
end Nonsmooth
