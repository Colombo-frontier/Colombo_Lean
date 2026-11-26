import RandomizedFO2003.CascadeStationarity

namespace RandomizedFO2003.Cascade

/-- Fixed numerical thresholds; none depends on a block, a dimension, or an algorithm. -/
def saturationThreshold : ℝ := 12416
def forcingOffset : ℝ := 12419
def forcingAmplitude : ℝ := 24836

noncomputable def radiusCoefficient : ℝ := 2 + 64 * forcingAmplitude * gateGradientConstant

theorem radiusCoefficient_pos : 0 < radiusCoefficient := by
  have hG := gateGradientConstant_pos
  unfold radiusCoefficient forcingAmplitude
  positivity

theorem parameter_radius_bound {h γ ε : ℝ} (hh : 0 < h) (hγ : 0 < γ)
    (hH : 512 * ε ≤ h) :
    ε + h + (h ^ 2 / γ) * (forcingOffset + saturationThreshold + 1) *
      (gateGradientConstant / (h / (64 * γ))) ≤ γ * (radiusCoefficient * h / γ) := by
  have he : ε ≤ h := by linarith
  have hout : (h ^ 2 / γ) * (forcingOffset + saturationThreshold + 1) *
      (gateGradientConstant / (h / (64 * γ))) = 64 * forcingAmplitude * gateGradientConstant * h := by
    unfold forcingOffset saturationThreshold forcingAmplitude
    field_simp
    ring
  have hr : γ * (radiusCoefficient * h / γ) = radiusCoefficient * h := by field_simp
  rw [hout, hr]
  unfold radiusCoefficient
  nlinarith

theorem parameter_a_error {h γ ε : ℝ} (hh : 0 < h) (hγ : 0 < γ)
    (hH : 512 * ε ≤ h) : γ⁻¹ * ε / (h / (64 * γ)) ≤ 1 / 8 := by
  have heq : γ⁻¹ * ε / (h / (64 * γ)) = 64 * ε / h := by field_simp; ring
  rw [heq]
  apply (div_le_iff₀ hh).mpr
  linarith

theorem parameter_b_error {h γ ε : ℝ} (hh : 0 < h) (hγ : 0 < γ)
    (hH : 512 * ε ≤ h) : h * γ⁻¹ * ε / (h ^ 2 / γ) ≤ 1 := by
  have heq : h * γ⁻¹ * ε / (h ^ 2 / γ) = ε / h := by field_simp; ring
  rw [heq]
  apply (div_le_one hh).mpr
  linarith

end RandomizedFO2003.Cascade
