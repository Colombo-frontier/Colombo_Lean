import SecondOrder.UniformOracleSuccess
import SecondOrder.CurvatureHolderSmallness

open MeasureTheory

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] {m T : ℕ}

theorem richAlgorithmSospProbability_curvature (μ : Measure Ξ)
    (alg : Ξ → RichAlgorithm (CurvatureDimension m T) S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : CurvatureCoefficients m T R) (N : ℕ) :
    richAlgorithmSospProbability μ (curvatureCoefficientLaw Θ R hR).toMeasure alg
      (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) ε γ N=
    curvatureSeededSospProbability μ (fun ξ => oracleAlgorithmPolicy (alg ξ) N)
      Θ A β R hR ε γ a₀ N :=
  oracleAlgorithmSuccessProbability_finite_policy μ (curvatureCoefficientLaw Θ R hR)
    alg (fun x a => richReply (scaledCurvatureSample Θ A β) a x) a₀ N
    (IsSOSP (scaledCurvaturePopulation Θ A β) ε γ)

theorem hvpAlgorithmSospProbability_curvature (μ : Measure Ξ)
    (alg : Ξ → HvpAlgorithm (CurvatureDimension m T) S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : CurvatureCoefficients m T R) (N : ℕ) :
    hvpAlgorithmSospProbability μ (curvatureCoefficientLaw Θ R hR).toMeasure alg
      (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) ε γ N=
    curvatureSeededSospProbability μ (fun ξ => hvpAlgorithmRichPolicy (alg ξ) N)
      Θ A β R hR ε γ a₀ N := by
  rw [←hvpAlgorithmSospProbability_simulation]
  exact richAlgorithmSospProbability_curvature μ _ Θ A β R hR ε γ a₀ N

end
end SecondOrder
