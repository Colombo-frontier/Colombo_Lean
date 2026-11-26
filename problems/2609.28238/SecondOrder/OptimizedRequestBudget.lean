import SecondOrder.EpochOptimization

namespace SecondOrder
noncomputable section

def mixedTrackingCost (P : Parameters) (τ γ : ℝ) : ℝ :=
  P.gap*chordVarianceScale P/(τ^2*γ)

def optimizedTrackingScale (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  1+P.gradientNoise^2/τ^2+idealMoveBudget P ν τ γ+balancedEpochCost P τ+
    epochTreeCoefficient P τ+mixedTrackingCost P τ γ

theorem mixedTrackingCost_pos (P : Parameters) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) :
    0 < mixedTrackingCost P τ γ := by
  have hΔ := P.gap_pos
  have hV := chordVarianceScale_pos P
  unfold mixedTrackingCost
  positivity

theorem optimizedTrackingScale_pos (P : Parameters) (ν : ℝ) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) :
    0 < optimizedTrackingScale P ν τ γ := by
  have hB := idealMoveBudget_nonneg P ν τ γ hγ
  have ho := balancedEpochCost_pos P hτ
  have he := epochTreeCoefficient_pos P hτ
  have hm := mixedTrackingCost_pos P hτ hγ
  unfold optimizedTrackingScale
  positivity

theorem gradientMoveBound_le_idealMoveBudget (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    P.gap*P.gradientLip/τ^2 ≤ idealMoveBudget P ν τ γ := by
  have hg : P.gap/(τ^2/P.gradientLip) = P.gap*P.gradientLip/τ^2 := by rw [div_div_eq_mul_div]
  rw [idealMoveBudget,hg]
  have hn : 0 ≤ P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2/16) := by
    exact div_nonneg P.gap_pos.le (by positivity)
  exact le_add_of_nonneg_right hn

/-- Exact expansion after the chord tolerance τ/(4L) is substituted. -/
theorem trackingRequestBudget_expansion (P : Parameters) (ν : ℝ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (δ : ℝ) {q L : ℕ} (hq : 0 < q) (hL : 0 < L) (κ : ℕ) :
    trackingRequestBudget P ν τ γ (τ/(4*(L : ℝ))) δ q L κ =
      (576*(P.gradientNoise^2/τ^2)+2+576*(epochAnchorCoefficient P τ/(q : ℝ))+
        2*((P.gap*P.gradientLip/τ^2)/(q : ℝ))+
        1152*(L : ℝ)^3*(epochTreeCoefficient P τ*(q : ℝ))+
        6144*(L : ℝ)^3*mixedTrackingCost P τ γ+4*idealMoveBudget P ν τ γ)*
          (8*Real.log (1/δ)+2)+
      (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ) := by
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hLip := P.gradientLip_pos
  unfold trackingRequestBudget
  congr 1
  unfold epochTreeBudget chordCostCoefficient epochAnchorCoefficient epochTreeCoefficient mixedTrackingCost chordVarianceScale
  field_simp
  <;> ring

theorem optimizedPrice_polynomial {a m o b v X Y z t : ℝ}
    (ha : 0 ≤ a) (hm : 0 ≤ m) (ho : 0 ≤ o) (hb : 0 ≤ b)
    (hX : 0 ≤ X) (ht : 1 ≤ t) (hz : z ≤ m) (hXY : X+Y ≤ 4*o+2*b+2*a) :
    576*a+2+576*X+2*z+1152*t*Y+6144*t*v+4*m ≤ 6144*t*(1+a+m+o+b+v) := by
  have htn : 0 ≤ t := by linarith
  have hw : 576*X+1152*t*Y ≤ 1152*t*(X+Y) := by
    have hx := mul_nonneg (show 0 ≤ 1152*t-576 by linarith) hX
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hXY (show 0 ≤ 1152*t by positivity)
  have ha' := mul_nonneg (sub_nonneg.mpr ht) ha
  have hm' := mul_nonneg (sub_nonneg.mpr ht) hm
  have ho' := mul_nonneg htn ho
  have hb' := mul_nonneg htn hb
  nlinarith

/-- Explicit optimized price with a cubic depth factor and the actual
local-confidence logarithm. The curvature contribution retains κ. -/
theorem trackingRequestBudget_optimized (P : Parameters) (ν : ℝ) {τ γ δ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {L : ℕ} (hL : 0 < L) (κ : ℕ) :
    trackingRequestBudget P ν τ γ (τ/(4*(L : ℝ))) δ (trackingEpochLength P τ) L κ ≤
      6144*(L : ℝ)^3*(8*Real.log (1/δ)+2)*optimizedTrackingScale P ν τ γ+
        (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ) := by
  have hq := trackingEpochLength_pos P τ
  have hqr : (1 : ℝ) ≤ trackingEpochLength P τ := by exact_mod_cast hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ht : (1 : ℝ) ≤ (L : ℝ)^3 := one_le_pow₀ hLr
  have ha : 0 ≤ P.gradientNoise^2/τ^2 := by positivity
  have hm := idealMoveBudget_nonneg P ν τ γ hγ
  have ho := (balancedEpochCost_pos P hτ).le
  have hb := (epochTreeCoefficient_pos P hτ).le
  have hX : 0 ≤ epochAnchorCoefficient P τ/(trackingEpochLength P τ : ℝ) :=
    div_nonneg (epochAnchorCoefficient_pos P hτ).le (Nat.cast_nonneg _)
  have hz : (P.gap*P.gradientLip/τ^2)/(trackingEpochLength P τ : ℝ) ≤ idealMoveBudget P ν τ γ :=
    (div_le_self (by exact div_nonneg (mul_nonneg P.gap_pos.le P.gradientLip_pos.le) (sq_nonneg _)) hqr).trans
      (gradientMoveBound_le_idealMoveBudget P ν τ hγ)
  have hp := optimizedPrice_polynomial (v := mixedTrackingCost P τ γ) ha hm ho hb hX ht hz
    (trackingEpochLength_cost P hτ)
  rw [trackingRequestBudget_expansion P ν hτ hγ δ hq hL κ]
  apply add_le_add_right
  have he := mul_le_mul_of_nonneg_right hp (chordConfidenceFactor_nonneg hδ hδ1)
  simpa only [optimizedTrackingScale] using he.trans_eq (by ring)

/-- The selected integer query cap has a deterministic explicit bound;
the +1 is the actual ceiling overhead. -/
theorem selectedQueryCap_bound (P : Parameters) (ν : ℝ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (κ : ℕ) :
    let M := physicalCap P ν τ γ
    let L := trackingTreeDepth M
    let δ := localFailureTolerance M
    (selectedQueryCap P ν τ γ κ : ℝ) <
      25+24*(6144*(L : ℝ)^3*(8*Real.log (1/δ)+2)*optimizedTrackingScale P ν τ γ+
        (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ)) := by
  dsimp only
  have hB := trackingRequestBudget_nonneg P ν τ γ (trackingChordTolerance τ (physicalCap P ν τ γ))
    (localFailureTolerance (physicalCap P ν τ γ)) (trackingEpochLength P τ)
    (trackingTreeDepth (physicalCap P ν τ γ)) κ hγ (localFailureTolerance_pos _) (localFailureTolerance_le_one _)
  have he := Nat.ceil_lt_add_one (show 0 ≤ 24*(1+trackingRequestBudget P ν τ γ
    (trackingChordTolerance τ (physicalCap P ν τ γ)) (localFailureTolerance (physicalCap P ν τ γ))
    (trackingEpochLength P τ) (trackingTreeDepth (physicalCap P ν τ γ)) κ) by positivity)
  have hp := trackingRequestBudget_optimized P ν hτ hγ (localFailureTolerance_pos (physicalCap P ν τ γ))
    (localFailureTolerance_le_one _) (trackingTreeDepth_pos (physicalCap P ν τ γ)) κ
  change trackingRequestBudget P ν τ γ (trackingChordTolerance τ (physicalCap P ν τ γ)) _ _ _ _ ≤ _ at hp
  change (selectedQueryCap P ν τ γ κ : ℝ) < _ at he
  linarith

end
end SecondOrder
