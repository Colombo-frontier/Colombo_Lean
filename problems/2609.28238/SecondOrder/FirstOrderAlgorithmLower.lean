import SecondOrder.FirstOrderAlgorithmProbability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

theorem firstOrderHvp_query_lower (P : Parameters) {ε ν : ℝ} (hc : FirstOrderHolderConditions P ε ν)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → HvpAlgorithm
      (FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
        (firstOrderEndpointLinks P.gap ε)) S)
    (halg : MeasurableOracleAlgorithmFamily alg) (γ : ℝ) (N : ℕ)
    (hs : HvpSolves μ alg P ν ε γ N) :
    firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) ε<(N:ℝ) := by
  let a₀ : FirstOrderCoefficients
      (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
      (firstOrderEndpointLinks P.gap ε)
      (firstOrderCoefficientScale (firstOrderHolderNoiseBudget P) (firstOrderOutputScale ε)) := Classical.choice inferInstance
  apply firstOrderHolderEndpoint_query_lower P hc μ (fun ξ => hvpAlgorithmRichPolicy (alg ξ) N)
    (hvpAlgorithmRichPolicy_measurable alg halg N) a₀ γ N
  dsimp only
  intro hR Θ hm
  rw [←hvpAlgorithmSospProbability_firstOrder μ alg Θ _ _ _ hR ε γ a₀ N]
  exact hs _ inferInstance _ inferInstance _ _ hm

theorem firstOrderRich_query_lower (P : Parameters) {σ₀ ε : ℝ} (hc : FirstOrderEndpointConditions P σ₀ ε)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → RichAlgorithm
      (FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
        (firstOrderEndpointLinks P.gap ε)) S)
    (halg : MeasurableOracleAlgorithmFamily alg) (γ : ℝ) (N : ℕ)
    (hs : RichSolves μ alg P σ₀ ε γ N) :
    firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) ε<(N:ℝ) := by
  let a₀ : FirstOrderCoefficients
      (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
      (firstOrderEndpointLinks P.gap ε)
      (firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε)) := Classical.choice inferInstance
  apply firstOrderEndpoint_query_lower P hc μ (fun ξ => oracleAlgorithmPolicy (alg ξ) N)
    (oracleAlgorithmPolicy_measurable alg halg N) a₀ γ N
  dsimp only
  intro hR Θ hm
  rw [←richAlgorithmSospProbability_firstOrder μ alg Θ _ _ _ hR ε γ a₀ N]
  exact hs _ inferInstance _ inferInstance _ _ hm

end
end SecondOrder
