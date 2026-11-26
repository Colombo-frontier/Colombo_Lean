import SecondOrder.HolderCostScaling

namespace SecondOrder
noncomputable section

/-- A tolerance-independent coefficient for the non-curvature-call work. -/
def endpointTrackingCoefficient (P : Parameters) (ν : ℝ) : ℝ :=
  1+P.gradientNoise^2+(P.gap*P.gradientLip+curvatureCountCoefficient P ν)+
    P.gap*P.gradientNoise*Real.sqrt (chordVarianceScale P)+P.gap*chordVarianceScale P/P.gradientLip+
    P.gap*chordVarianceScale P

theorem endpointTrackingCoefficient_pos (P : Parameters) (ν : ℝ) :
    0 < endpointTrackingCoefficient P ν := by
  have hΔ := P.gap_pos
  have hσ := P.gradientNoise_pos
  have hLip := P.gradientLip_pos
  have hV := chordVarianceScale_pos P
  have hC := curvatureCountCoefficient_pos P ν
  unfold endpointTrackingCoefficient
  positivity

theorem idealMoveBudget_endpoint (P : Parameters) {ν τ γ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    idealMoveBudget P ν τ γ ≤ (P.gap*P.gradientLip+curvatureCountCoefficient P ν)*holderEndpointRate ν τ γ := by
  have he : γ^(-holderRateExponent ν) ≤ holderEndpointRate ν τ γ :=
    le_add_of_nonneg_left (by positivity)
  have hg := mul_le_mul_of_nonneg_left (inv_sq_le_holderEndpointRate ν hτ hτ1 hγ)
    (mul_nonneg P.gap_pos.le P.gradientLip_pos.le)
  have hc := mul_le_mul_of_nonneg_left ((curvatureMovePower_le_endpoint ν hγ hγ1).trans he)
    (curvatureCountCoefficient_pos P ν).le
  rw [idealMoveBudget_scale P ν τ hγ]
  simpa only [mul_one_div,add_mul] using add_le_add hg hc

/-- Every actual optimized tracking term is bounded by the two endpoint
powers. The mixed τ⁻²γ⁻¹ term uses the manuscript's case split. -/
theorem optimizedTrackingScale_endpoint (P : Parameters) {ν τ γ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    optimizedTrackingScale P ν τ γ ≤ endpointTrackingCoefficient P ν*holderEndpointRate ν τ γ := by
  have hΔ := P.gap_pos
  have hσ := P.gradientNoise_pos
  have hLip := P.gradientLip_pos
  have hV := chordVarianceScale_pos P
  have h0 := one_le_holderEndpointRate ν hτ hτ1 hγ
  have hsq := inv_sq_le_holderEndpointRate ν hτ hτ1 hγ
  have hcub : 1/τ^3 ≤ holderEndpointRate ν τ γ := le_add_of_nonneg_right (Real.rpow_nonneg hγ.le _)
  have ha : P.gradientNoise^2/τ^2 ≤ P.gradientNoise^2*holderEndpointRate ν τ γ := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsq (sq_nonneg P.gradientNoise)
  have hm := idealMoveBudget_endpoint P (ν := ν) hτ hτ1 hγ hγ1
  have hb : balancedEpochCost P τ ≤
      (P.gap*P.gradientNoise*Real.sqrt (chordVarianceScale P))*holderEndpointRate ν τ γ := by
    simpa only [balancedEpochCost,mul_one_div] using
      mul_le_mul_of_nonneg_left hcub (by positivity : 0 ≤ P.gap*P.gradientNoise*Real.sqrt (chordVarianceScale P))
  have ht : epochTreeCoefficient P τ ≤
      (P.gap*chordVarianceScale P/P.gradientLip)*holderEndpointRate ν τ γ := by
    simpa only [epochTreeCoefficient,mul_one_div,div_div] using
      mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ P.gap*chordVarianceScale P/P.gradientLip)
  have hx : mixedTrackingCost P τ γ ≤ (P.gap*chordVarianceScale P)*holderEndpointRate ν τ γ := by
    simpa only [mixedTrackingCost,holderEndpointRate,holderRateExponent,mul_one_div] using
      mul_le_mul_of_nonneg_left (mixed_term_le_holder_endpoints hτ hγ hγ1 hν)
        (by positivity : 0 ≤ P.gap*chordVarianceScale P)
  unfold optimizedTrackingScale endpointTrackingCoefficient
  nlinarith

/-- Conditional cost conversion only: a separately verified single-call
price κ ≤ E/γ² gives the curvature endpoint. This does not construct an
eigensolver or prove that price hypothesis. -/
theorem curvatureRequestFactor_endpoint (P : Parameters) {ν τ γ E : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E/γ^2) :
    (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ) ≤
      E*(1+curvatureCountCoefficient P ν)*holderEndpointRate ν τ γ := by
  rw [curvatureCountScale_eq P ν hγ]
  have hC := curvatureCountCoefficient_pos P ν
  have hgpow := Real.rpow_pos_of_pos hγ (-(1+2/ν))
  have hpow : γ^(-holderRateExponent ν) ≤ holderEndpointRate ν τ γ := le_add_of_nonneg_left (by positivity)
  have hf : (1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))/γ^2 ≤
      (1+curvatureCountCoefficient P ν)*γ^(-holderRateExponent ν) := by
    rw [add_div,mul_div_assoc,curvatureMovePower_div_sq ν hγ]
    have hs := inv_gamma_sq_le_endpoint hν hγ hγ1
    nlinarith
  calc
    _ ≤ (1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))*(E/γ^2) :=
      mul_le_mul_of_nonneg_left hκ (by positivity)
    _ = E*((1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))/γ^2) := by ring
    _ ≤ E*((1+curvatureCountCoefficient P ν)*γ^(-holderRateExponent ν)) :=
      mul_le_mul_of_nonneg_left hf hE
    _ = (E*(1+curvatureCountCoefficient P ν))*γ^(-holderRateExponent ν) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Endpoint powers for the actual selected integer query cap. Logarithmic
factors remain explicit, and the per-curvature price bound remains an input. -/
theorem selectedQueryCap_endpoint (P : Parameters) {ν τ γ E : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E/γ^2) :
    (selectedQueryCap P ν τ γ κ : ℝ) <
      (25+24*(6144*(depthLogEnvelope P ν τ γ)^3*confidenceLogEnvelope P ν τ γ*
        endpointTrackingCoefficient P ν+E*(1+curvatureCountCoefficient P ν)))*holderEndpointRate ν τ γ := by
  have hs := optimizedTrackingScale_endpoint P hν hτ hτ1 hγ hγ1
  have he := curvatureRequestFactor_endpoint P hν hτ hγ hγ1 hE hκ
  have h0 := one_le_holderEndpointRate ν hτ hτ1 hγ
  have hd := depthLogEnvelope_pos P ν τ hγ
  have hc := confidenceLogEnvelope_nonneg P ν τ hγ
  have ht := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 6144*(depthLogEnvelope P ν τ γ)^3*confidenceLogEnvelope P ν τ γ by positivity)
  have hcap := selectedQueryCap_log_bound P ν hτ hγ κ
  nlinarith

theorem holderEndpointRate_epsilon {ν ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    holderEndpointRate ν (ε/10) γ ≤ 1000*holderEndpointRate ν ε γ := by
  have he : 1/(ε/10)^3 = 1000*(1/ε^3) := by field_simp; ring
  unfold holderEndpointRate
  rw [he]
  have hg := Real.rpow_nonneg hγ.le (-holderRateExponent ν)
  nlinarith

end
end SecondOrder
