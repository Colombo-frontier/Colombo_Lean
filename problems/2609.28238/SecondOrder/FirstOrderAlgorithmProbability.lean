import SecondOrder.UniformOracleSuccess
import SecondOrder.FirstOrderHolderSmallness

open MeasureTheory

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] {d T : ℕ}

theorem richAlgorithmSospProbability_firstOrder (μ : Measure Ξ)
    (alg : Ξ → RichAlgorithm (FirstOrderDimension d T) S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ) :
    richAlgorithmSospProbability μ (firstOrderChainCoefficientLaw Θ R hR).toMeasure alg
      (scaledFirstOrderPopulation Θ A β) (scaledFirstOrderSample Θ A β) ε γ N=
    firstOrderSeededSospProbability μ (fun ξ => oracleAlgorithmPolicy (alg ξ) N)
      Θ A β R hR ε γ a₀ N :=
  oracleAlgorithmSuccessProbability_finite_policy μ (firstOrderChainCoefficientLaw Θ R hR)
    alg (fun x a => richReply (scaledFirstOrderSample Θ A β) a x) a₀ N
    (IsSOSP (scaledFirstOrderPopulation Θ A β) ε γ)

theorem hvpAlgorithmSospProbability_firstOrder (μ : Measure Ξ)
    (alg : Ξ → HvpAlgorithm (FirstOrderDimension d T) S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ) :
    hvpAlgorithmSospProbability μ (firstOrderChainCoefficientLaw Θ R hR).toMeasure alg
      (scaledFirstOrderPopulation Θ A β) (scaledFirstOrderSample Θ A β) ε γ N=
    firstOrderSeededSospProbability μ (fun ξ => hvpAlgorithmRichPolicy (alg ξ) N)
      Θ A β R hR ε γ a₀ N := by
  rw [←hvpAlgorithmSospProbability_simulation]
  exact richAlgorithmSospProbability_firstOrder μ _ Θ A β R hR ε γ a₀ N

end
end SecondOrder
