import SecondOrder.FirstOrderEndpointAsymptotics

namespace SecondOrder
noncomputable section

def firstOrderHolderNoiseBudget (P : Parameters) : ℝ := firstOrderNoiseBudget P P.gradientNoise

def firstOrderHolderCoefficient (P : Parameters) (ε ν : ℝ) : ℝ :=
  (2*(firstOrderOutputScale ε*firstOrderGeometryConstant))^(1-ν)*
    (firstOrderOutputScale ε*(firstOrderGeometryConstant*
      Real.sqrt (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)))^ν

structure FirstOrderHolderConditions (P : Parameters) (ε ν : ℝ) : Prop where
  tolerance_pos : 0<ε
  nu_pos : 0<ν
  nu_le_one : ν≤1
  noise_small : 4*firstOrderNoiseConstant*firstOrderOutputScale ε≤firstOrderHolderNoiseBudget P
  gradient_small : firstOrderOutputScale ε*firstOrderGeometryConstant≤P.gradientLip
  hessian_small : firstOrderHolderCoefficient P ε ν≤P.hessianHolder
  gap_large : 160*firstOrderOutputScale ε≤P.gap
  stage_large : 32768≤(firstOrderCoefficientScale (firstOrderHolderNoiseBudget P) (firstOrderOutputScale ε))^2

theorem firstOrderHolderFamily_admissible (P : Parameters) {ε ν : ℝ} (hc : FirstOrderHolderConditions P ε ν)
    (Θ : Fin (firstOrderEndpointLinks P.gap ε+1) →
      Fin (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε) → Bool) :
    CommonLoss (firstOrderChainCoefficientLaw Θ
      (firstOrderCoefficientScale (firstOrderHolderNoiseBudget P) (firstOrderOutputScale ε))
      (firstOrderCoefficientScale_ge_two (firstOrderOutputScale_pos hc.tolerance_pos) hc.noise_small)).toMeasure P ν
      (scaledFirstOrderPopulation Θ (firstOrderOutputScale ε) 1)
      (scaledFirstOrderSample Θ (firstOrderOutputScale ε) 1) := by
  have hd := (firstOrderEndpointBlockSize_bounds (s := firstOrderHolderNoiseBudget P)
    P.gap_pos.le hc.tolerance_pos).1
  have hA := firstOrderOutputScale_pos hc.tolerance_pos
  have hn := firstOrderScales_noise hA hc.noise_small
  have hb := firstOrderNoiseBudget_bounds P P.gradientNoise
  apply scaledFirstOrderCommonLoss Θ hd P hA.le (by norm_num) hc.nu_pos hc.nu_le_one _ _
  · have hh := firstOrderBudgetLinks_gap (Δ := P.gap) hA (by linarith only [hc.gap_large,hA])
    exact hh.trans (by linarith only [P.gap_pos])
  · simpa only [one_pow,mul_one] using hc.gradient_small
  · simpa only [one_pow,mul_one,firstOrderHolderCoefficient] using hc.hessian_small
  · simpa only [mul_one] using hn.trans hb.2.1
  · simpa only [one_pow,mul_one] using hn.trans hb.2.2

end
end SecondOrder
