import SecondOrder.CurvatureAlgorithmProbability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

theorem curvatureHvp_query_lower (P : Parameters) {γ ν : ℝ} (hc : CurvatureHolderConditions P γ ν)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → HvpAlgorithm
      (CurvatureDimension (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
        (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)) S)
    (halg : MeasurableOracleAlgorithmFamily alg) (ε : ℝ) (N : ℕ)
    (hs : HvpSolves μ alg P ν ε γ N) :
    curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν<(N:ℝ) := by
  let a₀ : CurvatureCoefficients
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ) := Classical.choice inferInstance
  apply curvatureHolderEndpoint_query_lower P hc μ (fun ξ => hvpAlgorithmRichPolicy (alg ξ) N)
    (hvpAlgorithmRichPolicy_measurable alg halg N) a₀ ε N
  dsimp only
  intro hR Θ hm
  rw [←hvpAlgorithmSospProbability_curvature μ alg Θ _ _ _ hR ε γ a₀ N]
  exact hs _ inferInstance _ inferInstance _ _ hm

theorem curvatureRich_query_lower (P : Parameters) {σ₀ γ : ℝ} (hc : CurvatureEndpointConditions P σ₀ γ)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → RichAlgorithm
      (CurvatureDimension (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
        (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)) S)
    (halg : MeasurableOracleAlgorithmFamily alg) (ε : ℝ) (N : ℕ)
    (hs : RichSolves μ alg P σ₀ ε γ N) :
    curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ<(N:ℝ) := by
  let a₀ : CurvatureCoefficients
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ) := Classical.choice inferInstance
  apply curvatureEndpoint_query_lower P hc μ (fun ξ => oracleAlgorithmPolicy (alg ξ) N)
    (oracleAlgorithmPolicy_measurable alg halg N) a₀ ε N
  dsimp only
  intro hR Θ hm
  rw [←richAlgorithmSospProbability_curvature μ alg Θ _ _ _ hR ε γ a₀ N]
  exact hs _ inferInstance _ inferInstance _ _ hm

end
end SecondOrder
