import NCBall.ChargeParameters

/-! # Two-sided natural-radius bounds for the actual chain -/

noncomputable section
namespace NCBall

theorem calibrated_radius_bounds {γ H Δ : ℝ} (hγ : 0 < γ) (hH : 0 < H) (_hΔ : 0 ≤ Δ)
    (hregime : 200 * bumpConstant * γ ^ 2 ≤ H * Δ) :
    37 * Δ / (100 * γ) ≤ 37 * calibratedDepth γ H Δ * calibratedRho γ H ∧
      37 * calibratedDepth γ H Δ * calibratedRho γ H ≤ 37 * Δ / (50 * γ) := by
  have hC := bumpConstant_pos
  have hρ := calibratedRho_pos hγ hH
  let a := H * Δ / (100 * bumpConstant * γ ^ 2)
  have ha : 2 ≤ a := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * bumpConstant * γ ^ 2)).mpr
    nlinarith
  have hlo : a / 2 ≤ (calibratedDepth γ H Δ : ℝ) := nat_floor_half ha
  have hhi : (calibratedDepth γ H Δ : ℝ) ≤ a := Nat.floor_le (by positivity)
  constructor
  · calc
      _ = (a / 2) * (37 * calibratedRho γ H) := by
        dsimp [a, calibratedRho]
        field_simp
        ring
      _ ≤ (calibratedDepth γ H Δ : ℝ) * (37 * calibratedRho γ H) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      _ = _ := by ring
  · calc
      _ = (calibratedDepth γ H Δ : ℝ) * (37 * calibratedRho γ H) := by ring
      _ ≤ a * (37 * calibratedRho γ H) := mul_le_mul_of_nonneg_right hhi (by positivity)
      _ = _ := by
        dsimp [a, calibratedRho]
        field_simp
        ring

end NCBall
