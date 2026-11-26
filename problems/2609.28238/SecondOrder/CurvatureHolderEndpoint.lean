import SecondOrder.CurvatureHolderDimension

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- Explicit finite-parameter sufficient conditions for the Hölder endpoint.
No value-noise condition is needed in this oracle model. -/
structure CurvatureHolderConditions (P : Parameters) (γ ν : ℝ) : Prop where
  tolerance_pos : 0<γ
  nu_pos : 0<ν
  nu_le_one : ν≤1
  hessian_noise_small : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P
  gradient_small : 8*curvatureGeometryConstant*γ≤P.gradientLip
  gradient_noise_small : curvatureNoiseBudget P*
      Real.sqrt (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)≤
    P.gradientNoise*curvatureHolderInputScale P.hessianHolder γ ν
  gap_large : 8*curvatureOutputScale
    (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
    (curvatureHolderEffectiveL P.hessianHolder γ ν) γ≤P.gap
  stage_large : 131072*(curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν:ℝ)≤
    (curvatureCoefficientScale (curvatureNoiseBudget P) γ)^2

variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- A single admissible Hölder instance defeats the whole private-seed
randomized policy below the explicit γ^{-(3+2/ν)} threshold. -/
theorem curvatureHolderEndpoint_lower (P : Parameters) {γ ν : ℝ} (hc : CurvatureHolderConditions P γ ν)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → CurvaturePolicy
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : CurvatureCoefficients
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureCoefficientScale (curvatureNoiseBudget P) γ))
    (N : ℕ) (hN : (N:ℝ)≤curvatureHolderThreshold P.gap P.hessianHolder (curvatureNoiseBudget P)
      (curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν) γ ν) :
    let m := curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
    let D : ℝ := curvatureHolderBlockSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
    let T := curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
    let L' := curvatureHolderEffectiveL P.hessianHolder γ ν
    let A := curvatureOutputScale D L' γ
    let β := curvatureInputScale L' γ
    let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
    ∃ (hR : 2≤R) (Θ : Fin (T+1) → BalancedVector m),
      CommonLoss (curvatureCoefficientLaw Θ R hR).toMeasure P ν
        (scaledCurvaturePopulation Θ A β) (scaledCurvatureSample Θ A β) ∧
      curvatureSeededSuccessProbability μ alg Θ A β R hR
        (fun Θ x => HasSecondOrderCertificate (scaledCurvaturePopulation Θ A β) γ x) a₀ N<1/4 := by
  let m := curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν
  let D : ℝ := (2*m:ℕ)
  let L' := curvatureHolderEffectiveL P.hessianHolder γ ν
  let A := curvatureOutputScale D L' γ
  let R := curvatureCoefficientScale (curvatureNoiseBudget P) γ
  let T := curvatureBudgetLinks P.gap A
  let cap := curvatureResponseCap D R
  have hd := curvatureEndpointHalfSize_bounds (L := L') (σ := curvatureNoiseBudget P) P.gap_pos.le hc.tolerance_pos
  have hm : 0<m := lt_of_lt_of_le (by norm_num : (0:ℕ)<4) hd.1
  have hD : 0<D := by
    change (0:ℝ)<((2*m:ℕ):ℝ)
    exact_mod_cast Nat.mul_pos (by omega) hm
  have hL' : 0<L' := curvatureHolderEffectiveL_pos P.hessianHolder_pos hc.tolerance_pos
  have hA : 0<A := curvatureOutputScale_pos hD hL' hc.tolerance_pos
  have hsize : 8*A≤P.gap := hc.gap_large
  have hT : 0<T := (curvatureBudgetLinks_lower hA hc.gap_large).1
  have hcap0 : 0<cap := (curvatureResponseCap_bounds hD hc.stage_large).1
  have hR : 2≤R := curvatureCoefficientScale_ge_two hc.tolerance_pos hc.hessian_noise_small
  have hN' := hN
  rw [←curvatureHolderThreshold_identity P.hessianHolder_pos hc.tolerance_pos] at hN'
  have hbudget : 2*N≤T*cap := curvatureEndpointThreshold_budget hL' hD hc.tolerance_pos hc.gap_large hc.stage_large N hN'
  obtain ⟨hhorizon,hlarge,hfar⟩ := curvatureHolder_horizon P.hessianHolder_pos hc.tolerance_pos hc.gap_large N hN
  have hinfo := curvatureResponseCap_information hm hR
  have hmean := curvatureSeeded_success_one_eighth μ alg halg hm hT A (curvatureInputScale L' γ)
    R hR cap hcap0 (0,0,0) a₀ N hbudget hhorizon hlarge hinfo hfar
    (fun Θ x => HasSecondOrderCertificate (scaledCurvaturePopulation Θ A (curvatureInputScale L' γ)) γ x)
    (fun Θ => hasSecondOrderCertificate_measurableSet
      ((scaledCurvaturePopulation_contDiff Θ A _).of_le (show (2:WithTop ℕ∞)≤3 by decide)) γ)
    (fun Θ x hx => curvatureHardFamily_secondOrder_progress Θ hm hL' hc.tolerance_pos hx)
  obtain ⟨Θ,hΘ⟩ := exists_below_pmfMean_bound (curvatureHiddenPrior m T) _
    (lt_of_le_of_lt hmean (show (1:ℝ)/8<1/4 by norm_num))
  refine ⟨hR,Θ,?_,hΘ⟩
  exact curvatureHolderBudgetFamily_admissible hm P hc.tolerance_pos hc.nu_pos hc.nu_le_one
    hc.hessian_noise_small hc.gradient_small hc.gradient_noise_small
    (by linarith only [hsize,hA]) Θ

theorem curvatureHolderEndpoint_dimension (P : Parameters) {γ ν : ℝ} (hc : CurvatureHolderConditions P γ ν) :
    ((CurvatureDimension
      (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
      (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν):ℕ):ℝ)≤
      P.gap*P.hessianHolder^(2/ν)/
        (16*(32*curvatureGeometryConstant)^(2/ν)*γ^(1+2/ν)) := by
  have hd := curvatureEndpointHalfSize_bounds
    (L := curvatureHolderEffectiveL P.hessianHolder γ ν) (σ := curvatureNoiseBudget P)
    P.gap_pos.le hc.tolerance_pos
  have hm : 0<curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν := by
    dsimp [curvatureHolderHalfSize]; omega
  have hD : (0:ℝ)<((2*curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν:ℕ):ℝ) :=
    by exact_mod_cast Nat.mul_pos (by omega) hm
  have hA := curvatureOutputScale_pos hD
    (curvatureHolderEffectiveL_pos (ν := ν) P.hessianHolder_pos hc.tolerance_pos) hc.tolerance_pos
  have hsize := hc.gap_large
  simp only [curvatureHolderBlockSize] at hsize
  exact curvatureHolderBudgetLinks_dimension hm P.hessianHolder_pos hc.tolerance_pos
    (by linarith only [hsize,hA])

end
end SecondOrder
