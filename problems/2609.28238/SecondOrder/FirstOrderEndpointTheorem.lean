import SecondOrder.FirstOrderEndpointSmallness

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- Explicit universal constants in the first-order endpoint's three
small-tolerance conditions. The gap condition is equivalent to Δ/ε≥1/c. -/
structure FirstOrderEndpointConditions (P : Parameters) (σ₀ ε : ℝ) : Prop where
  valueNoise_pos : 0<σ₀
  tolerance_pos : 0<ε
  gradient_small : ε≤firstOrderEndpointSmallConstant*P.gradientLip
  noise_small : ε≤firstOrderEndpointSmallConstant*firstOrderNoiseBudget P σ₀
  hessian_small : ε*Real.sqrt (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)≤
    firstOrderEndpointSmallConstant*P.hessianHolder
  gap_large : ε≤firstOrderEndpointSmallConstant*P.gap

variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- For any randomized measurable policy below the explicit epsilon^{-3}
threshold, one admissible conservative rich instance defeats its gradient task.
The probability includes both private randomness and fresh oracle samples. -/
theorem firstOrderEndpoint_lower (P : Parameters) {σ₀ ε : ℝ} (hc : FirstOrderEndpointConditions P σ₀ ε)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (alg : Ξ → FirstOrderPolicy
      (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
      (firstOrderEndpointLinks P.gap ε) S)
    (halg : MeasurableQueryPolicyFamily alg)
    (a₀ : FirstOrderCoefficients
      (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
      (firstOrderEndpointLinks P.gap ε)
      (firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε)))
    (N : ℕ) (hN : (N:ℝ)≤firstOrderEndpointThreshold P.gap (firstOrderNoiseBudget P σ₀) ε) :
    let d := firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε
    let T := firstOrderEndpointLinks P.gap ε
    let A := firstOrderOutputScale ε
    let R := firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) A
    ∃ (hR : 2≤R) (Θ : Fin (T+1) → Fin d → Bool),
      RichCommonLoss (firstOrderChainCoefficientLaw Θ R hR).toMeasure P σ₀
        (scaledFirstOrderPopulation Θ A 1) (scaledFirstOrderSample Θ A 1) ∧
      firstOrderSeededGradientProbability μ alg Θ A 1 R hR ε a₀ N<1/4 := by
  let d := firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε
  let A := firstOrderOutputScale ε
  let R := firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) A
  let T := firstOrderBudgetLinks P.gap A
  let cap := firstOrderResponseCap R
  have hd : 0<d := (firstOrderEndpointBlockSize_bounds P.gap_pos.le hc.tolerance_pos).1
  obtain ⟨hsmall,hLip,hHolder,hsize,hcap⟩ := firstOrderEndpoint_smallness P hc.valueNoise_pos
    (Nat.cast_nonneg d) hc.tolerance_pos hc.gradient_small hc.noise_small hc.hessian_small hc.gap_large
  have hA : 0<A := firstOrderOutputScale_pos hc.tolerance_pos
  have hT : 0<T := (firstOrderBudgetLinks_lower hA hsize).1
  have hcap0 : 0<cap := (firstOrderResponseCap_bounds hcap).1
  have hR : 2≤R := firstOrderCoefficientScale_ge_two hA hsmall
  have hbudget : 2*N≤T*cap := firstOrderEndpointThreshold_query_budget hc.tolerance_pos hsize hcap N hN
  obtain ⟨hhorizon,hlarge,hfar⟩ := firstOrderEndpoint_horizon hc.tolerance_pos hsize N hN
  have hinfo := firstOrderResponseCap_information d hR
  have hsep : ε<A*1*firstOrderGradientConstant := by
    rw [mul_one,firstOrderOutputScale_separation]
    linarith only [hc.tolerance_pos]
  obtain ⟨Θ,hΘ⟩ := firstOrderSeeded_exists_gradient_hard_target μ alg halg hd hT hA.le
    (by norm_num : (0:ℝ)≤1) hsep R hR cap hcap0 (0,0,0) a₀ N
    hbudget hhorizon hlarge hinfo hfar
  refine ⟨hR,Θ,?_,hΘ⟩
  apply firstOrderHardFamily_admissible Θ hd P hc.valueNoise_pos hc.tolerance_pos hsmall _ hLip hHolder
  have hgap := firstOrderBudgetLinks_gap (Δ := P.gap) hA (by linarith only [hsize,hA])
  exact hgap.trans (by linarith only [P.gap_pos])

theorem firstOrderEndpoint_dimension (P : Parameters) {σ₀ ε : ℝ} (hc : FirstOrderEndpointConditions P σ₀ ε) :
    (FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
      (firstOrderEndpointLinks P.gap ε):ℝ)≤
      (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε:ℝ)*P.gap/ε := by
  let d := firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε
  let A := firstOrderOutputScale ε
  obtain ⟨_,_,_,hsize,_⟩ := firstOrderEndpoint_smallness P hc.valueNoise_pos
    (Nat.cast_nonneg d) hc.tolerance_pos hc.gradient_small hc.noise_small hc.hessian_small hc.gap_large
  have hA : 0<A := firstOrderOutputScale_pos hc.tolerance_pos
  have hn := firstOrderBudgetLinks_count (Δ := P.gap) hA (by linarith only [hsize,hA])
  have hf := Nat.floor_le (div_nonneg P.gap_pos.le (by positivity : 0≤40*A))
  have hden : ε≤40*A := by
    have hg := firstOrderGradientConstant_le_one
    have he := firstOrderOutputScale_separation ε
    nlinarith [mul_le_mul_of_nonneg_left hg hA.le]
  have hq := hf.trans (div_le_div_of_nonneg_left P.gap_pos.le hc.tolerance_pos hden)
  rw [←hn] at hq
  have hh := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg d : (0:ℝ)≤d)
  change (((firstOrderBudgetLinks P.gap A+1)*d:ℕ):ℝ)≤(d:ℝ)*P.gap/ε
  convert hh using 1 <;> push_cast <;> ring

end
end SecondOrder
