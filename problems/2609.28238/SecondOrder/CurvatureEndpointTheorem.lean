import SecondOrder.CurvatureRandomizedSuccess

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def curvatureEndpointBlockSize (Δ L σ γ : ℝ) : ℕ := 2*curvatureEndpointHalfSize Δ L σ γ

def curvatureEndpointLinks (Δ L σ γ : ℝ) : ℕ :=
  curvatureBudgetLinks Δ (curvatureOutputScale (curvatureEndpointBlockSize Δ L σ γ) L γ)

/-- Explicit versions of the manuscript's five small-tolerance conditions.
The block size is chosen from the stated logarithmic expression. -/
structure CurvatureEndpointConditions (P : Parameters) (σ₀ γ : ℝ) : Prop where
  valueNoise_pos : 0<σ₀
  tolerance_pos : 0<γ
  gradient_small : γ≤curvatureEndpointSmallConstant*P.gradientLip
  noise_small : γ*Real.sqrt (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)≤
    curvatureEndpointSmallConstant*curvatureNoiseBudget P
  gradient_noise_small : curvatureNoiseBudget P*γ*
      Real.sqrt (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)≤
    curvatureEndpointSmallConstant*(P.hessianHolder*P.gradientNoise)
  value_noise_small : (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ:ℝ)*
      (curvatureNoiseBudget P*γ^2+γ^3)≤curvatureEndpointSmallConstant*(σ₀*P.hessianHolder^2)
  gap_large : (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ:ℝ)*γ^3≤
    curvatureEndpointSmallConstant*(P.gap*P.hessianHolder^2)

variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- Quantitative curvature endpoint for the actual conservative rich loss.
Every randomized measurable N-query policy below the displayed tolerance
threshold fails even the Hessian-only task on one admissible hidden instance. -/
theorem curvatureEndpoint_lower (P : Parameters) {σ₀ γ : ℝ} (hc : CurvatureEndpointConditions P σ₀ γ)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → CurvaturePolicy
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : CurvatureCoefficients
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ))
    (N : ℕ) (hN : (N:ℝ)≤curvatureEndpointThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ) γ) :
    let m := curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
    let D : ℝ := curvatureEndpointBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
    let T := curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ
    let A := curvatureOutputScale D P.hessianHolder γ
    let β := curvatureInputScale P.hessianHolder γ
    let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
    ∃ (hR : 2≤R) (Θ : Fin (T+1) → BalancedVector m),
      RichCommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P σ₀
        (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) ∧
      curvatureSeededSuccessProbability μ alg Θ A β R hR
        (fun Θ x => HasSecondOrderCertificate (scaledCurvaturePopulation Θ A β) γ x) a₀ N<1/4 := by
  let m := curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ
  let D : ℝ := (2*m:ℕ)
  let A := curvatureOutputScale D P.hessianHolder γ
  let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
  let T := curvatureBudgetLinks P.gap A
  let cap := curvatureResponseCap D R
  have hd := curvatureEndpointHalfSize_bounds (L := P.hessianHolder) (σ := curvatureNoiseBudget P) P.gap_pos.le hc.tolerance_pos
  have hm : 0<m := by dsimp [m]; omega
  have hD : 1≤D := by
    change (1:ℝ)≤((2*m:ℕ):ℝ)
    exact_mod_cast (show 1≤2*m by omega)
  have hD0 : 0<D := lt_of_lt_of_le (by norm_num) hD
  obtain ⟨hsmall,hLip,hgrad,hvalue,hsize,hcap⟩ := curvatureEndpoint_smallness P hc.valueNoise_pos hD hc.tolerance_pos
    hc.gradient_small hc.noise_small hc.gradient_noise_small hc.value_noise_small hc.gap_large
  have hA : 0<A := curvatureOutputScale_pos hD0 P.hessianHolder_pos hc.tolerance_pos
  have hT : 0<T := (curvatureBudgetLinks_lower hA hsize).1
  have hcap0 : 0<cap := (curvatureResponseCap_bounds hD0 hcap).1
  have hR : 2≤R := curvatureCoefficientScale_ge_two hc.tolerance_pos hsmall
  have hbudget : 2*N≤T*cap := curvatureEndpointThreshold_budget P.hessianHolder_pos hD0 hc.tolerance_pos hsize hcap N hN
  obtain ⟨hhorizon,hlarge,hfar⟩ := curvatureEndpoint_horizon P.hessianHolder_pos hc.tolerance_pos hsize N hN
  have hinfo := curvatureResponseCap_information hm hR
  have hmean := curvatureSeeded_success_one_eighth μ alg halg hm hT A (curvatureInputScale P.hessianHolder γ)
    R hR cap hcap0 (0,0,0) a₀ N hbudget hhorizon hlarge hinfo hfar
    (fun Θ x => HasSecondOrderCertificate (scaledCurvaturePopulation Θ A (curvatureInputScale P.hessianHolder γ)) γ x)
    (fun Θ => hasSecondOrderCertificate_measurableSet
      ((scaledCurvaturePopulation_contDiff Θ A _).of_le (show (2:WithTop ℕ∞)≤3 by decide)) γ)
    (fun Θ x hx => curvatureHardFamily_secondOrder_progress Θ hm P.hessianHolder_pos hc.tolerance_pos hx)
  obtain ⟨Θ,hΘ⟩ := exists_below_pmfMean_bound (curvatureHiddenPrior m T) _
    (lt_of_le_of_lt hmean (show (1:ℝ)/8<1/4 by norm_num))
  refine ⟨hR,Θ,?_,hΘ⟩
  exact curvatureBudgetFamily_admissible hm P hc.valueNoise_pos hc.tolerance_pos hsmall hLip hgrad hvalue
    (by linarith only [hsize,hA]) Θ

theorem curvatureEndpoint_dimension (P : Parameters) {σ₀ γ : ℝ} (hc : CurvatureEndpointConditions P σ₀ γ) :
    ((CurvatureDimension
      (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
      (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ):ℕ):ℝ)≤
      P.gap*P.hessianHolder^2/(4096*curvatureGeometryConstant^2*γ^3) := by
  have hd := curvatureEndpointHalfSize_bounds (L := P.hessianHolder) (σ := curvatureNoiseBudget P) P.gap_pos.le hc.tolerance_pos
  have hm : 0<curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ := by omega
  have hD : (1:ℝ)≤((2*curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ:ℕ):ℝ) :=
    by exact_mod_cast (show 1≤2*curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ by omega)
  have hs := curvatureEndpoint_smallness P hc.valueNoise_pos hD hc.tolerance_pos
    hc.gradient_small hc.noise_small hc.gradient_noise_small hc.value_noise_small hc.gap_large
  have hA := curvatureOutputScale_pos (lt_of_lt_of_le (by norm_num) hD) P.hessianHolder_pos hc.tolerance_pos
  exact curvatureBudgetLinks_dimension hm P.hessianHolder_pos hc.tolerance_pos
    (by linarith only [hs.2.2.2.2.1,hA])

end
end SecondOrder
