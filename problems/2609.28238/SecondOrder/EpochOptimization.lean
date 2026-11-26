import SecondOrder.TrackingParameters

namespace SecondOrder
noncomputable section

def epochAnchorCoefficient (P : Parameters) (τ : ℝ) : ℝ :=
  P.gap*P.gradientNoise^2*P.gradientLip/τ^4

def epochTreeCoefficient (P : Parameters) (τ : ℝ) : ℝ :=
  P.gap*chordVarianceScale P/(P.gradientLip*τ^2)

def balancedEpochCost (P : Parameters) (τ : ℝ) : ℝ :=
  P.gap*P.gradientNoise*Real.sqrt (chordVarianceScale P)/τ^3

theorem epochAnchorCoefficient_pos (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    0 < epochAnchorCoefficient P τ := by
  have hΔ := P.gap_pos
  have hσ := P.gradientNoise_pos
  have hLip := P.gradientLip_pos
  unfold epochAnchorCoefficient
  positivity

theorem epochTreeCoefficient_pos (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    0 < epochTreeCoefficient P τ := by
  have hΔ := P.gap_pos
  have hV := chordVarianceScale_pos P
  have hLip := P.gradientLip_pos
  unfold epochTreeCoefficient
  positivity

theorem balancedEpochCost_pos (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    0 < balancedEpochCost P τ := by
  have hΔ := P.gap_pos
  have hσ := P.gradientNoise_pos
  have hV := Real.sqrt_pos.mpr (chordVarianceScale_pos P)
  unfold balancedEpochCost
  positivity

/-- The manuscript's q⋆ exactly balances the two q-dependent terms. -/
theorem preferredEpochLength_balance (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    epochAnchorCoefficient P τ = epochTreeCoefficient P τ*(preferredEpochLength P τ)^2 := by
  have hV := chordVarianceScale_pos P
  have hLip := P.gradientLip_pos
  unfold epochAnchorCoefficient epochTreeCoefficient preferredEpochLength
  simp only [div_pow,mul_pow,Real.sq_sqrt hV.le]
  field_simp
  <;> ring

theorem preferredEpochLength_cost (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    epochTreeCoefficient P τ*preferredEpochLength P τ = balancedEpochCost P τ := by
  have hV := chordVarianceScale_pos P
  have hs := Real.sqrt_pos.mpr hV
  have hLip := P.gradientLip_pos
  calc
    _ = P.gap*P.gradientNoise*(Real.sqrt (chordVarianceScale P))^2/
        (Real.sqrt (chordVarianceScale P)*τ^3) := by
      rw [Real.sq_sqrt hV.le]
      unfold epochTreeCoefficient preferredEpochLength
      field_simp
      <;> ring
    _ = _ := by
      unfold balancedEpochCost
      field_simp
      ring_nf
      rw [Real.sq_sqrt hV.le]
      ring

/-- The upper clipping endpoint is paid by the initial-anchor scale. -/
theorem epochAnchorCoefficient_cap (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    epochAnchorCoefficient P τ/(epochGradientCap P τ : ℝ) ≤ P.gradientNoise^2/τ^2 := by
  have hN : (0 : ℝ) < epochGradientCap P τ := Nat.cast_pos.mpr (epochGradientCap_pos P τ)
  have hc : P.gap*P.gradientLip/τ^2 ≤ (epochGradientCap P τ : ℝ) := by
    have he := epochGradientCap_lower P τ
    linarith
  apply (div_le_iff₀ hN).mpr
  calc
    _ = (P.gradientNoise^2/τ^2)*(P.gap*P.gradientLip/τ^2) := by
      unfold epochAnchorCoefficient
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

/-- Fully discrete optimization, with explicit costs for either clipped
endpoint and the upward rounding of an interior minimizer. -/
theorem trackingEpochLength_cost (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    epochAnchorCoefficient P τ/(trackingEpochLength P τ : ℝ)+
      epochTreeCoefficient P τ*(trackingEpochLength P τ : ℝ) ≤
        4*balancedEpochCost P τ+2*epochTreeCoefficient P τ+2*(P.gradientNoise^2/τ^2) := by
  have hb := clippedCeil_balance (epochAnchorCoefficient_pos P hτ).le (epochTreeCoefficient_pos P hτ).le
    (preferredEpochLength_pos P hτ) (epochGradientCap_pos P τ) (preferredEpochLength_balance P hτ)
  change epochAnchorCoefficient P τ/(trackingEpochLength P τ : ℝ)+
    epochTreeCoefficient P τ*(trackingEpochLength P τ : ℝ) ≤ _ at hb
  rw [mul_assoc,preferredEpochLength_cost P hτ] at hb
  simp only [mul_div_assoc] at hb
  have hc := epochAnchorCoefficient_cap P hτ
  linarith

end
end SecondOrder
