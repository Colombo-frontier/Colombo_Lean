import SecondOrder.CurvatureHolderEndpoint

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- The Hölder curvature endpoint in explicit query-complexity form.
The success premise concerns the actual full value/gradient/Hessian reply. -/
theorem curvatureHolderEndpoint_query_lower (P : Parameters) {γ ν : ℝ} (hc : CurvatureHolderConditions P γ ν)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → CurvaturePolicy
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : CurvatureCoefficients
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ)) (ε : ℝ) (N : ℕ)
    (hsuccess :
      let m := curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
      let D : ℝ := curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
      let T := curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
      let L' := curvatureHolderEffectiveL P.hessianHolder γ ν
      let A := curvatureOutputScale D L' γ
      let β := curvatureInputScale L' γ
      let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
      ∀ (hR : 2≤R) (Θ : Fin (T+1) → BalancedVector m),
        CommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P ν
          (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) →
        2/3≤curvatureSeededSospProbability μ alg Θ A β R hR ε γ a₀ N) :
    curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν<(N:ℝ) := by
  by_contra hN
  obtain ⟨hR,Θ,hmodel,hbad⟩ := curvatureHolderEndpoint_lower P hc μ alg halg a₀ N (le_of_not_gt hN)
  have hgood := hsuccess hR Θ hmodel
  have hmono := curvatureSeededSospProbability_le_secondOrder μ alg Θ
    (curvatureOutputScale (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderEffectiveL P.hessianHolder γ ν) γ)
    (curvatureInputScale (curvatureHolderEffectiveL P.hessianHolder γ ν) γ) _ hR ε γ a₀ N
  linarith only [hgood,hmono,hbad]

end
end SecondOrder
