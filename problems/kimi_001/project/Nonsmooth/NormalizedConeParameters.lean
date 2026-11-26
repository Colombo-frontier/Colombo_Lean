import Nonsmooth.DimensionCircularPrecision
import Mathlib.Tactic

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem normalized_cone_query_radius {r : ℝ} (hr : 0 < r) (d : ℕ) (hd : 0 < d) :
    0 < r / (4 * (d : ℝ)) ∧ r / (4 * (d : ℝ)) ≤ r := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (d : ℝ))).mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hd1)]

theorem normalized_cone_cap_threshold {r : ℝ} (hr : 0 ≤ r) (d : ℕ) (hd : 0 < d) :
    r / (8 * (d : ℝ)) + (1 / (16 * (d : ℝ) ^ 2)) *
      ((d : ℝ) * r + r / (8 * (d : ℝ))) ≤ r / (4 * (d : ℝ)) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ : (1 / (16 * (d : ℝ) ^ 2) : ℝ) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (d : ℝ) ^ 2)
      (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith
  have hb0 : 0 ≤ r / (8 * (d : ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_right hδ hb0
  have heq : (1 / (16 * (d : ℝ) ^ 2)) * ((d : ℝ) * r) = r / (16 * (d : ℝ)) := by
    field_simp
  rw [mul_add, heq]
  calc
    _ ≤ r / (8 * (d : ℝ)) + r / (16 * (d : ℝ)) + (1 / 16) * (r / (8 * (d : ℝ))) := by linarith
    _ = (25 / 32 : ℝ) * (r / (4 * (d : ℝ))) := by field_simp; ring
    _ ≤ r / (4 * (d : ℝ)) := by
      have hp : 0 ≤ r / (4 * (d : ℝ)) := by positivity
      nlinarith

theorem normalized_cone_precision_scale (d : ℕ) : d ≤ 4 * d ^ 2 := by nlinarith

theorem normalized_cone_precision_log_bound (d : ℕ) :
    Real.log (((4 * d ^ 2 : ℕ) : ℝ) + 1) ≤ 4 * Real.log ((d : ℝ) + 1) := by
  have hnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpoly : 0 ≤ (d : ℝ) ^ 4 + 4 * (d : ℝ) ^ 3 + 2 * (d : ℝ) ^ 2 + 4 * (d : ℝ) := by positivity
  have hle : (4 : ℝ) * (d : ℝ) ^ 2 + 1 ≤ ((d : ℝ) + 1) ^ 4 := by nlinarith only [hpoly]
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 4 * (d : ℝ) ^ 2 + 1) hle
  rw [Real.log_pow] at hl
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hl

end
end Nonsmooth
