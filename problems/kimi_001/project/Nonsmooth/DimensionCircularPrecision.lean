import Nonsmooth.CircularWideConePolicy
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def dimensionCircularPrecision (D : ℕ) : ℕ := 5 + 2 * Nat.clog 2 D

theorem dimensionCircularPrecision_power (D : ℕ) :
    32 * (D : ℝ) ^ 2 ≤ (2 : ℝ) ^ dimensionCircularPrecision D := by
  have hp : (D : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 D := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) D
  have he : (2 : ℝ) ^ dimensionCircularPrecision D = 32 * ((2 : ℝ) ^ Nat.clog 2 D) ^ 2 := by
    simp only [dimensionCircularPrecision, pow_add]
    rw [mul_comm 2 (Nat.clog 2 D), pow_mul]
    norm_num
  rw [he]
  nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D,
    show (0 : ℝ) ≤ 2 ^ Nat.clog 2 D by positivity]

theorem dimensionCircularPrecision_slope (D : ℕ) (hD : 0 < D) :
    2 / (2 : ℝ) ^ dimensionCircularPrecision D ≤ (1 / (8 * (D : ℝ) ^ 2)) / 2 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ dimensionCircularPrecision D)
    (by positivity : (0 : ℝ) < 8 * (D : ℝ) ^ 2 * 2)).mpr
  nlinarith only [dimensionCircularPrecision_power D]

theorem natClog_two_le_one_add_two_log (D : ℕ) (hD : 0 < D) :
    (Nat.clog 2 D : ℝ) ≤ 1 + 2 * Real.log D := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hD1)
  have hceil : ⌈Real.logb 2 (D : ℝ)⌉₊ = Nat.clog 2 D := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 D
  rw [hceil] at hc
  have hdiv : Real.log D / Real.log 2 ≤ 2 * Real.log D := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith [mul_nonneg hlogD (sub_nonneg.mpr hlog2)]
  change (Nat.clog 2 D : ℝ) < Real.log D / Real.log 2 + 1 at hc
  linarith

/-- Each circular stage, including initialization, costs at most 62 log(D+1) responses. -/
theorem dimensionCircularPrecision_query_bound (D : ℕ) (hD : 0 < D) :
    ((3 * dimensionCircularPrecision D + 4 : ℕ) : ℝ) ≤ 62 * Real.log ((D : ℝ) + 1) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hc := natClog_two_le_one_add_two_log D hD
  have hmono : Real.log D ≤ Real.log ((D : ℝ) + 1) := Real.log_le_log hDpos (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hbase : (1 / 2 : ℝ) ≤ Real.log ((D : ℝ) + 1) :=
    hlog2.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith))
  simp only [dimensionCircularPrecision, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

end
end Nonsmooth
