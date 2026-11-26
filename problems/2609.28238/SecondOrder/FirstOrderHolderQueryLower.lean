import SecondOrder.FirstOrderHolderEndpoint

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- Uniform success on admissible Hölder instances forces the explicit
epsilon^{-3} query bound, for every second-order tolerance gamma. -/
theorem firstOrderHolderEndpoint_query_lower (P : Parameters) {ε ν : ℝ} (hc : FirstOrderHolderConditions P ε ν)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → FirstOrderPolicy
      (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
      (firstOrderEndpointLinks P.gap ε) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : FirstOrderCoefficients
      (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
      (firstOrderEndpointLinks P.gap ε)
      (firstOrderCoefficientScale (firstOrderHolderNoiseBudget P) (firstOrderOutputScale ε)))
    (γ : ℝ) (N : ℕ)
    (hsuccess :
      let d := firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε
      let T := firstOrderEndpointLinks P.gap ε
      let A := firstOrderOutputScale ε
      let R := firstOrderCoefficientScale (firstOrderHolderNoiseBudget P) A
      ∀ (hR : 2≤R) (Θ : Fin (T+1) → Fin d → Bool),
        CommonLoss (firstOrderChainCoefficientLaw Θ R hR).toMeasure P ν
          (scaledFirstOrderPopulation Θ A 1) (scaledFirstOrderSample Θ A 1) →
        2/3≤firstOrderSeededSospProbability μ alg Θ A 1 R hR ε γ a₀ N) :
    firstOrderEndpointThreshold P.gap (firstOrderHolderNoiseBudget P) ε<(N:ℝ) := by
  by_contra hN
  obtain ⟨hR,Θ,hmodel,hbad⟩ := firstOrderHolderEndpoint_lower P hc μ alg halg a₀ N (le_of_not_gt hN)
  have hgood := hsuccess hR Θ hmodel
  have hmono := firstOrderSeededSospProbability_le_gradient μ alg Θ (firstOrderOutputScale ε) 1 _ hR ε γ a₀ N
  linarith only [hgood,hmono,hbad]

end
end SecondOrder
