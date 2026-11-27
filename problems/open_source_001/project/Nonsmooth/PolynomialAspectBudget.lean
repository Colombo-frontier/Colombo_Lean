import Nonsmooth.AspectConeParameters

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem polynomial_aspect_positive (d : ℕ) (hd : 0 < d) : 0 < 4 * d ^ 3 := by positivity

theorem polynomial_aspect_radius (d : ℕ) (hd : 0 < d) :
    ((4 * d ^ 3 : ℕ) : ℝ) * (1 / (d : ℝ)) = 4 * (d : ℝ) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

theorem polynomial_aspect_log_bound (d : ℕ) (hd : 0 < d) :
    Real.log (((4 * d ^ 3 : ℕ) : ℝ) + 1) ≤ 5 * Real.log ((d : ℝ) + 1) := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hbound : (4 : ℝ) * (d : ℝ) ^ 3 + 1 ≤ ((d : ℝ) + 1) ^ 5 := by
    nlinarith [pow_nonneg hd0 5, pow_nonneg hd0 4, pow_nonneg hd0 3, sq_nonneg (d : ℝ)]
  have h := Real.log_le_log (show (0 : ℝ) < 4 * (d : ℝ) ^ 3 + 1 by positivity) hbound
  rw [Real.log_pow] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using h

theorem polynomial_aspect_local_budget_bound (d : ℕ) (hd : 0 < d) :
    62 * (d : ℝ) * (2 * Real.log ((d : ℝ) + 1) +
      Real.log (((4 * d ^ 3 : ℕ) : ℝ) + 1)) ≤
      434 * (d : ℝ) * Real.log ((d : ℝ) + 1) := by
  have h := mul_le_mul_of_nonneg_left (polynomial_aspect_log_bound d hd)
    (by positivity : 0 ≤ 62 * (d : ℝ))
  nlinarith

end
end Nonsmooth
