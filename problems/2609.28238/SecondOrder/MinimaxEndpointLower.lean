import SecondOrder.MinimaxComplexity

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

theorem firstOrderHvp_minimax_lower (P : Parameters) {ε ν : ℝ} (hc : FirstOrderHolderConditions P ε ν) (γ : ℝ) :
    ENNReal.ofReal (firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) ε)≤
      hvpMinimaxComplexity P ν
        (FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
          (firstOrderEndpointLinks P.gap ε)) ε γ := by
  apply hvpMinimaxComplexity_lower
  intro N hN
  rcases hN with ⟨Ξ,S,mΞ,mS,μ,hμ,alg,halg,hs⟩
  exact (firstOrderHvp_query_lower P hc μ alg halg γ N hs).le

theorem firstOrderRich_minimax_lower (P : Parameters) {σ₀ ε : ℝ} (hc : FirstOrderEndpointConditions P σ₀ ε) (γ : ℝ) :
    ENNReal.ofReal (firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) ε)≤
      richMinimaxComplexity P σ₀
        (FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
          (firstOrderEndpointLinks P.gap ε)) ε γ := by
  apply richMinimaxComplexity_lower
  intro N hN
  rcases hN with ⟨Ξ,S,mΞ,mS,μ,hμ,alg,halg,hs⟩
  exact (firstOrderRich_query_lower P hc μ alg halg γ N hs).le

theorem curvatureHvp_minimax_lower (P : Parameters) {γ ν : ℝ} (hc : CurvatureHolderConditions P γ ν) (ε : ℝ) :
    ENNReal.ofReal (curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν)≤
      hvpMinimaxComplexity P ν
        (CurvatureDimension (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
          (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)) ε γ := by
  apply hvpMinimaxComplexity_lower
  intro N hN
  rcases hN with ⟨Ξ,S,mΞ,mS,μ,hμ,alg,halg,hs⟩
  exact (curvatureHvp_query_lower P hc μ alg halg ε N hs).le

theorem curvatureRich_minimax_lower (P : Parameters) {σ₀ γ : ℝ} (hc : CurvatureEndpointConditions P σ₀ γ) (ε : ℝ) :
    ENNReal.ofReal (curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ)≤
      richMinimaxComplexity P σ₀
        (CurvatureDimension (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
          (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)) ε γ := by
  apply richMinimaxComplexity_lower
  intro N hN
  rcases hN with ⟨Ξ,S,mΞ,mS,μ,hμ,alg,halg,hs⟩
  exact (curvatureRich_query_lower P hc μ alg halg ε N hs).le

theorem half_sum_le_max (a b : ℝ) : (a+b)/2≤max a b := by
  have ha := le_max_left a b
  have hb := le_max_right a b
  linarith

/-- The paper takes a supremum over dimensions. The two hard families can
therefore use different dimensions inside the same envelope. -/
theorem hvpEnvelopeComplexity_two_lower (P : Parameters) (ν κ ε γ : ℝ)
    (d₁ d₂ : ℕ) (hd₁ : 1≤d₁) (hd₂ : 1≤d₂)
    (hD₁ : d₁≤toleranceDimensionEnvelope κ ε γ) (hD₂ : d₂≤toleranceDimensionEnvelope κ ε γ)
    (a b : ℝ) (ha : ENNReal.ofReal a≤hvpMinimaxComplexity P ν d₁ ε γ)
    (hb : ENNReal.ofReal b≤hvpMinimaxComplexity P ν d₂ ε γ) :
    ENNReal.ofReal ((a+b)/2)≤hvpEnvelopeComplexity P ν κ ε γ := by
  apply (ENNReal.ofReal_le_ofReal (half_sum_le_max a b)).trans
  rcases le_total a b with hab|hba
  · rw [max_eq_right hab]
    exact hb.trans (hvpMinimaxComplexity_le_envelope P ν κ ε γ d₂ hd₂ hD₂)
  · rw [max_eq_left hba]
    exact ha.trans (hvpMinimaxComplexity_le_envelope P ν κ ε γ d₁ hd₁ hD₁)

theorem richEnvelopeComplexity_two_lower (P : Parameters) (σ₀ κ ε γ : ℝ)
    (d₁ d₂ : ℕ) (hd₁ : 1≤d₁) (hd₂ : 1≤d₂)
    (hD₁ : d₁≤toleranceDimensionEnvelope κ ε γ) (hD₂ : d₂≤toleranceDimensionEnvelope κ ε γ)
    (a b : ℝ) (ha : ENNReal.ofReal a≤richMinimaxComplexity P σ₀ d₁ ε γ)
    (hb : ENNReal.ofReal b≤richMinimaxComplexity P σ₀ d₂ ε γ) :
    ENNReal.ofReal ((a+b)/2)≤richEnvelopeComplexity P σ₀ κ ε γ := by
  apply (ENNReal.ofReal_le_ofReal (half_sum_le_max a b)).trans
  rcases le_total a b with hab|hba
  · rw [max_eq_right hab]
    exact hb.trans (richMinimaxComplexity_le_envelope P σ₀ κ ε γ d₂ hd₂ hD₂)
  · rw [max_eq_left hba]
    exact ha.trans (richMinimaxComplexity_le_envelope P σ₀ κ ε γ d₁ hd₁ hD₁)

end
end SecondOrder
