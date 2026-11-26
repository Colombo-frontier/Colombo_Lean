import NoisyZO.Model

/-!
# Explicit projection onto the Euclidean unit ball

The projected algorithm uses the radial map `x ↦ x / max 1 ‖x‖`.
This file proves continuity, feasibility, and the Fejér inequality needed by
the projected-SGD recurrence.
-/

open scoped InnerProductSpace

namespace NoisyZO

noncomputable section

/-- Radial metric projection onto the closed Euclidean unit ball. -/
def unitBallProjection {d : ℕ} (x : Point d) : Point d :=
  (max 1 ‖x‖)⁻¹ • x

/-- The radial projection is continuous. -/
theorem continuous_unitBallProjection {d : ℕ} :
    Continuous (unitBallProjection : Point d → Point d) := by
  unfold unitBallProjection
  exact ((continuous_const.max continuous_norm).inv₀ fun x ↦ by
    positivity).smul continuous_id

/-- The radial projection always lies in the closed unit ball. -/
theorem norm_unitBallProjection_le_one {d : ℕ} (x : Point d) :
    ‖unitBallProjection x‖ ≤ 1 := by
  by_cases hx : ‖x‖ ≤ 1
  · simp [unitBallProjection, hx]
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    rw [unitBallProjection, max_eq_right hx'.le, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
      inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hx'))]

/-- Projection onto the unit ball cannot increase distance to any feasible
comparison point. -/
theorem norm_unitBallProjection_sub_le {d : ℕ} (x y : Point d)
    (hy : ‖y‖ ≤ 1) :
    ‖unitBallProjection x - y‖ ≤ ‖x - y‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · simp [unitBallProjection, max_eq_left hx]
  · have hs : 1 < ‖x‖ := lt_of_not_ge hx
    have hs0 : 0 < ‖x‖ := lt_trans zero_lt_one hs
    have hx0 : ‖x‖ ≠ 0 := ne_of_gt hs0
    rw [unitBallProjection, max_eq_right hs.le]
    have hprojNorm : ‖(‖x‖)⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
      exact inv_mul_cancel₀ hx0
    have hxy : ⟪x, y⟫_ℝ ≤ ‖x‖ := by
      calc
        ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
        _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg x)
        _ = ‖x‖ := mul_one _
    have hsq : ‖(‖x‖)⁻¹ • x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, hprojNorm]
      simp only [one_pow, real_inner_smul_left]
      have hfac :
          0 ≤ (‖x‖ - 1) * (‖x‖ * (‖x‖ + 1) - 2 * ⟪x, y⟫_ℝ) := by
        have hfirst : 0 ≤ ‖x‖ - 1 := sub_nonneg.2 hs.le
        have hsecond : 0 ≤ ‖x‖ * (‖x‖ + 1) - 2 * ⟪x, y⟫_ℝ := by
          nlinarith [mul_nonneg (norm_nonneg x) hfirst]
        exact mul_nonneg hfirst hsecond
      have hfacdiv :
          0 ≤ ((‖x‖ - 1) * (‖x‖ * (‖x‖ + 1) - 2 * ⟪x, y⟫_ℝ)) /
            ‖x‖ := div_nonneg hfac hs0.le
      have halg :
          (‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ) -
              (1 - 2 * ((‖x‖)⁻¹ * ⟪x, y⟫_ℝ)) =
            ((‖x‖ - 1) * (‖x‖ * (‖x‖ + 1) - 2 * ⟪x, y⟫_ℝ)) /
              ‖x‖ := by
        field_simp [hx0]
        ring
      nlinarith [hfacdiv]
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
    simpa only [pow_two] using hsq

end

end NoisyZO
