import SecondOrder.EpochMinimum
import SecondOrder.OptimizedRequestBudget
import SecondOrder.HolderCostScaling

namespace SecondOrder
noncomputable section

def minimumTrackingScale (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  1+P.gradientNoise^2/τ^2+idealMoveBudget P ν τ γ+epochMinimum P τ+mixedTrackingCost P τ γ

theorem minimumPrice_polynomial {a m e v X Y z t : ℝ}
    (ha : 0 ≤ a) (hm : 0 ≤ m) (he : 0 ≤ e) (hX : 0 ≤ X)
    (ht : 1 ≤ t) (hz : z ≤ m) (hXY : X+Y ≤ 2*e) :
    576*a+2+576*X+2*z+1152*t*Y+6144*t*v+4*m ≤
      6144*t*(1+a+m+e+v) := by
  have ht0 : 0 ≤ t := by linarith
  have hw : 576*X+1152*t*Y ≤ 1152*t*(X+Y) := by
    nlinarith [mul_nonneg (show 0 ≤ 1152*t-576 by linarith) hX]
  have hc := mul_le_mul_of_nonneg_left hXY (show 0 ≤ 1152*t by positivity)
  have ha' := mul_nonneg (sub_nonneg.mpr ht) ha
  have hm' := mul_nonneg (sub_nonneg.mpr ht) hm
  have he' := mul_nonneg ht0 he
  nlinarith

/-- Full dependence on the constrained optimum, including both clipped
regimes. No balanced-value or endpoint surcharge remains. -/
theorem trackingRequestBudget_minimum (P : Parameters) (ν : ℝ) {τ γ δ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ℕ} (hL : 0 < L) (κ : ℕ) :
    trackingRequestBudget P ν τ γ (τ/(4*(L : ℝ))) δ (trackingEpochLength P τ) L κ ≤
      6144*(L : ℝ)^3*(8*Real.log (1/δ)+2)*minimumTrackingScale P ν τ γ+
        (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ) := by
  have hq := trackingEpochLength_pos P τ
  have hqr : (1 : ℝ) ≤ trackingEpochLength P τ := by exact_mod_cast hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hz : (P.gap*P.gradientLip/τ^2)/(trackingEpochLength P τ : ℝ) ≤ idealMoveBudget P ν τ γ :=
    (div_le_self (div_nonneg (mul_nonneg P.gap_pos.le P.gradientLip_pos.le) (sq_nonneg _)) hqr).trans
      (gradientMoveBound_le_idealMoveBudget P ν τ hγ)
  have hp := minimumPrice_polynomial (v := mixedTrackingCost P τ γ)
    (by positivity : 0 ≤ P.gradientNoise^2/τ^2) (idealMoveBudget_nonneg P ν τ γ hγ)
    (epochMinimum_nonneg P hτ)
    (div_nonneg (epochAnchorCoefficient_pos P hτ).le (Nat.cast_nonneg _))
    (one_le_pow₀ hLr : (1:ℝ) ≤ (L:ℝ)^3) hz (trackingEpochLength_near_minimum P hτ)
  rw [trackingRequestBudget_expansion P ν hτ hγ δ hq hL κ]
  apply add_le_add_right
  have hh := mul_le_mul_of_nonneg_right hp (chordConfidenceFactor_nonneg hδ hδ1)
  exact hh.trans_eq (by unfold minimumTrackingScale; ring)

theorem selectedQueryCap_minimum_bound (P : Parameters) (ν : ℝ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (κ : ℕ) :
    let M := physicalCap P ν τ γ
    let L := trackingTreeDepth M
    let δ := localFailureTolerance M
    (selectedQueryCap P ν τ γ κ : ℝ) <
      25+24*(6144*(L : ℝ)^3*(8*Real.log (1/δ)+2)*minimumTrackingScale P ν τ γ+
        (1+curvatureCountCoefficient P ν*γ^(-(1+2/ν)))*(κ : ℝ)) := by
  dsimp only
  have hB := trackingRequestBudget_nonneg P ν τ γ (trackingChordTolerance τ (physicalCap P ν τ γ))
    (localFailureTolerance (physicalCap P ν τ γ)) (trackingEpochLength P τ)
    (trackingTreeDepth (physicalCap P ν τ γ)) κ hγ (localFailureTolerance_pos _) (localFailureTolerance_le_one _)
  have he := Nat.ceil_lt_add_one (show 0 ≤ 24*(1+trackingRequestBudget P ν τ γ
    (trackingChordTolerance τ (physicalCap P ν τ γ)) (localFailureTolerance (physicalCap P ν τ γ))
    (trackingEpochLength P τ) (trackingTreeDepth (physicalCap P ν τ γ)) κ) by positivity)
  have hp := trackingRequestBudget_minimum P ν hτ hγ (localFailureTolerance_pos (physicalCap P ν τ γ))
    (localFailureTolerance_le_one _) (trackingTreeDepth_pos (physicalCap P ν τ γ)) κ
  change trackingRequestBudget P ν τ γ (trackingChordTolerance τ (physicalCap P ν τ γ)) _ _ _ _ ≤ _ at hp
  change (selectedQueryCap P ν τ γ κ : ℝ) < _ at he
  rw [curvatureCountScale_eq P ν hγ] at hp
  linarith

theorem minimumTrackingScale_epsilon (P : Parameters) (ν : ℝ) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    minimumTrackingScale P ν (ε/10) γ ≤ 10000*minimumTrackingScale P ν ε γ := by
  have ha : P.gradientNoise^2/(ε/10)^2 = 100*(P.gradientNoise^2/ε^2) := by ring
  have hg : P.gap*P.gradientLip/(ε/10)^2 = 100*(P.gap*P.gradientLip/ε^2) := by ring
  have hv : mixedTrackingCost P (ε/10) γ = 100*mixedTrackingCost P ε γ := by
    unfold mixedTrackingCost
    ring
  have he := epochMinimum_epsilon_scale P hε
  have hK : 0 ≤ curvatureCountCoefficient P ν*γ^(-(1+2/ν)) :=
    mul_nonneg (curvatureCountCoefficient_pos P ν).le (Real.rpow_nonneg hγ.le _)
  have hA : 0 ≤ P.gradientNoise^2/ε^2 := by positivity
  have hG : 0 ≤ P.gap*P.gradientLip/ε^2 :=
    div_nonneg (mul_nonneg P.gap_pos.le P.gradientLip_pos.le) (sq_nonneg _)
  have hV := (mixedTrackingCost_pos P hε hγ).le
  unfold minimumTrackingScale
  rw [idealMoveBudget_scale P ν (ε/10) hγ, idealMoveBudget_scale P ν ε hγ, ha, hg, hv]
  linarith

end
end SecondOrder
