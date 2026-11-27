import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem grunbaum_scalar_constant_quarter (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hq
  have heq : (n : ℝ) * (1 - ((n : ℝ) / ((n : ℝ) + 1))⁻¹) = -1 := by
    field_simp
    ring
  have hlog : -1 ≤ Real.log (((n : ℝ) / ((n : ℝ) + 1)) ^ n) := by
    rw [Real.log_pow, ← heq]
    exact mul_le_mul_of_nonneg_left hl hnp.le
  have hexp : Real.exp (-1) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by
    simpa only [Real.exp_log (pow_pos hq n)] using Real.exp_le_exp.mpr hlog
  have hquarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos 1)).mpr
    have h := Real.exp_one_lt_d9
    nlinarith
  exact hquarter.trans hexp

end
end Nonsmooth
