import Nonsmooth.NormalizedConeParameters

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem aspect_cone_precision_scale (d A : ℕ) (hA : 0 < A) : d ≤ 4 * d * A := by nlinarith

theorem aspect_cone_cap_threshold {r : ℝ} (hr : 0 ≤ r) (d A : ℕ) (hd : 0 < d) (hA : 0 < A) :
    r / (8 * (d : ℝ)) + (1 / (16 * (d : ℝ) * (A : ℝ))) *
      ((A : ℝ) * r + r / (8 * (d : ℝ))) ≤ r / (4 * (d : ℝ)) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hprod : (1 : ℝ) ≤ (d : ℝ) * (A : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hA1)]
  have hδ : (1 / (16 * (d : ℝ) * (A : ℝ)) : ℝ) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (d : ℝ) * (A : ℝ))
      (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith only [hprod]
  have hb0 : 0 ≤ r / (8 * (d : ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_right hδ hb0
  have heq : (1 / (16 * (d : ℝ) * (A : ℝ))) * ((A : ℝ) * r) = r / (16 * (d : ℝ)) := by
    field_simp
  rw [mul_add, heq]
  calc
    _ ≤ r / (8 * (d : ℝ)) + r / (16 * (d : ℝ)) + (1 / 16) * (r / (8 * (d : ℝ))) := by linarith
    _ = (25 / 32 : ℝ) * (r / (4 * (d : ℝ))) := by field_simp; ring
    _ ≤ r / (4 * (d : ℝ)) := by
      have hp : 0 ≤ r / (4 * (d : ℝ)) := by positivity
      nlinarith

theorem aspect_cone_precision_log_bound (d A : ℕ) (hd : 0 < d) :
    Real.log (((4 * d * A : ℕ) : ℝ) + 1) ≤
      2 * Real.log ((d : ℝ) + 1) + Real.log ((A : ℝ) + 1) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hs : (4 : ℝ) * (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hm := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ (A : ℝ) + 1 by positivity)
  have hle : (4 : ℝ) * (d : ℝ) * (A : ℝ) + 1 ≤ ((d : ℝ) + 1) ^ 2 * ((A : ℝ) + 1) := by
    nlinarith only [hm, hd1]
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 4 * (d : ℝ) * (A : ℝ) + 1) hle
  rw [Real.log_mul (by positivity : ((d : ℝ) + 1) ^ 2 ≠ 0) (by positivity : (A : ℝ) + 1 ≠ 0),
    Real.log_pow] at hl
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hl

end
end Nonsmooth
