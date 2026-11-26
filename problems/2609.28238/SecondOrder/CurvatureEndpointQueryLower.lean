import SecondOrder.CurvatureEndpointTheorem

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {m T : ℕ}

theorem curvatureSeededSospProbability_le_secondOrder (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ) (a₀ : CurvatureCoefficients m T R) (N : ℕ) :
    curvatureSeededSospProbability μ P Θ A β R hR ε γ a₀ N≤
      curvatureSeededSuccessProbability μ P Θ A β R hR
        (fun Θ x => HasSecondOrderCertificate (scaledCurvaturePopulation Θ A β) γ x) a₀ N := by
  unfold curvatureSeededSospProbability curvatureSeededSuccessProbability
  exact measureReal_mono (fun w hw => hw.2)

/-- An algorithm that succeeds on every admissible member must exceed the
explicit curvature lower bound, for every first-order tolerance ε. -/
theorem curvatureEndpoint_query_lower (P : Parameters) {σ₀ γ : ℝ} (hc : CurvatureEndpointConditions P σ₀ γ)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → CurvaturePolicy
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : CurvatureCoefficients
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ)) (ε : ℝ) (N : ℕ)
    (hsuccess :
      let m := curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
      let D : ℝ := curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
      let T := curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ
      let A := curvatureOutputScale D P.hessianHolder γ
      let β := curvatureInputScale P.hessianHolder γ
      let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
      ∀ (hR : 2≤R) (Θ : Fin (T+1) → BalancedVector m),
        RichCommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P σ₀
          (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) →
        2/3≤curvatureSeededSospProbability μ alg Θ A β R hR ε γ a₀ N) :
    curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ<(N:ℝ) := by
  by_contra hN
  obtain ⟨hR,Θ,hmodel,hbad⟩ := curvatureEndpoint_lower P hc μ alg halg a₀ N (le_of_not_gt hN)
  have hgood := hsuccess hR Θ hmodel
  have hmono := curvatureSeededSospProbability_le_secondOrder μ alg Θ
    (curvatureOutputScale (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) P.hessianHolder γ)
    (curvatureInputScale P.hessianHolder γ) _ hR ε γ a₀ N
  linarith only [hgood,hmono,hbad]

end
end SecondOrder
