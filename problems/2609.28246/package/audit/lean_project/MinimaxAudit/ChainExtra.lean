import Mathlib
namespace MinimaxAudit

noncomputable def balancedQ (n : ℕ) : ℝ := 1 - 1 / (4 * (n + 1 : ℝ))

theorem balancedQ_nonneg (n : ℕ) : 0 ≤ balancedQ n := by
  unfold balancedQ
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) < 4 * (n + 1) := by positivity
  have h : (1 : ℝ) / (4 * (n + 1)) ≤ 1 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  linarith

theorem balancedQ_le_one (n : ℕ) : balancedQ n ≤ 1 := by
  unfold balancedQ
  have : (0 : ℝ) ≤ 1 / (4 * (n + 1)) := by positivity
  linarith

theorem balancedQ_power_lower (n : ℕ) : (3 : ℝ) / 4 ≤ balancedQ n ^ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) < 4 * (n + 1) := by positivity
  have hq := balancedQ_nonneg n
  have harg : (-2 : ℝ) ≤ -(1 / (4 * (n + 1 : ℝ))) := by
    unfold balancedQ at hq
    linarith
  have hb := one_add_mul_le_pow harg n
  have hfrac : (n : ℝ) / (4 * (n + 1)) ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have htarget := (show (3 : ℝ) / 4 ≤ 1 + (n : ℝ) * -(1 / (4 * (n + 1 : ℝ))) by
      rw [mul_neg, mul_one_div]
      linarith)
  simpa only [balancedQ, sub_eq_add_neg] using le_trans htarget hb

end MinimaxAudit

namespace MinimaxAudit

/-- In each block, `N` queries, one output vector and `N+1` frame vectors
fit in the manuscript's deterministic ambient dimension. -/
theorem deterministic_dimension_count (N : ℕ) :
    N + 1 + (N + 1) = 2 * N + 2 := by omega

/-- The orthogonality constraints before the `t`th reveal leave room for
all still unrevealed frame vectors in dimension `2N+2`. -/
theorem resisting_frame_room (N t : ℕ) (ht : t ≤ N) :
    t + t + (N + 1 - t) ≤ 2 * N + 2 := by omega

/-- Exact tangent-residual scaling. Here `s = sqrt(n)`, the derivative
order is `p = k+1`, and `s^(3*k+2) = n^((3*p-1)/2)`. This is an
algebraic identity for positive scales, not the analytic smoothness bound. -/
theorem tangent_scale_identity (L eta kappa R C s : ℝ) (k : ℕ)
    (hs : s ≠ 0) (hC : C ≠ 0) :
    (L * (eta * kappa * R / s ^ 3) ^ k / C) * (kappa * R / s) / s =
      L * eta ^ k * kappa ^ (k + 1) * R ^ (k + 1) /
        (C * s ^ (3 * k + 2)) := by
  simp only [div_pow, mul_pow, pow_add, pow_one, pow_mul]
  field_simp

/-- Exact saddle-gap scaling, with the same denominator as the tangent
scale and one extra factor of the radius. -/
theorem gap_scale_identity (L eta kappa R C s : ℝ) (k : ℕ)
    (hs : s ≠ 0) (hC : C ≠ 0) :
    (L * (eta * kappa * R / s ^ 3) ^ k / C) * (kappa * R / s) ^ 2 =
      L * eta ^ k * kappa ^ (k + 2) * R ^ (k + 2) /
        (C * s ^ (3 * k + 2)) := by
  simp only [div_pow, mul_pow, pow_add, pow_mul]
  field_simp

/-- The exact accuracy exponent after writing the chain length as
`sqrt(n)^2` and the oracle order as `k+1`. -/
theorem sqrt_power_accuracy_exponent (n : ℝ) (hn : 0 ≤ n) (k : ℕ) :
    (Real.sqrt n) ^ (3 * k + 2) =
      n ^ ((3 * ((k : ℝ) + 1) - 1) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hn]
  congr 1
  push_cast
  ring

end MinimaxAudit
