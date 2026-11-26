import SecondOrder.FirstOrderIntegerBudgets

namespace SecondOrder
noncomputable section

theorem firstOrderGradientConstant_le_one : firstOrderGradientConstant≤1 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  unfold firstOrderGradientConstant
  nlinarith

theorem firstOrderGeometryConstant_ge_one : 1≤firstOrderGeometryConstant := by
  norm_num [firstOrderGeometryConstant,firstOrderJetConstant,completionDerivativeBound]

theorem firstOrderNoiseConstant_ge_one : 1≤firstOrderNoiseConstant := by
  norm_num [firstOrderNoiseConstant]

theorem firstOrderEndpointThreshold_pos {Δ s ε : ℝ}
    (hΔ : 0<Δ) (hs : 0<s) (hε : 0<ε) : 0<firstOrderEndpointThreshold Δ s ε := by
  unfold firstOrderEndpointThreshold
  have hg := firstOrderGradientConstant_pos
  have hn := firstOrderNoiseConstant_pos
  positivity

theorem firstOrderEndpointThreshold_query_budget {Δ s ε : ℝ} (hε : 0<ε)
    (hsize : 160*firstOrderOutputScale ε≤Δ)
    (hcap : 32768≤(firstOrderCoefficientScale s (firstOrderOutputScale ε))^2)
    (N : ℕ) (hN : (N:ℝ)≤firstOrderEndpointThreshold Δ s ε) :
    2*N≤firstOrderBudgetLinks Δ (firstOrderOutputScale ε)*
      firstOrderResponseCap (firstOrderCoefficientScale s (firstOrderOutputScale ε)) := by
  have hh := firstOrderEndpointThreshold_budget hε hsize hcap
  have hb : (2:ℝ)*(N:ℝ)≤(firstOrderBudgetLinks Δ (firstOrderOutputScale ε):ℝ)*
      (firstOrderResponseCap (firstOrderCoefficientScale s (firstOrderOutputScale ε)):ℝ) := by
    linarith only [hN,hh]
  exact_mod_cast hb

theorem firstOrderEndpointThreshold_le_envelope {Δ s ε : ℝ} (hΔ : 0≤Δ) (hε : 0<ε) :
    firstOrderEndpointThreshold Δ s ε≤Δ*s^2/ε^3 := by
  have hg := firstOrderGradientConstant_le_one
  have hg0 := firstOrderGradientConstant_pos
  have hn := firstOrderNoiseConstant_ge_one
  have hg3 : firstOrderGradientConstant^3≤1 := by
    simpa using pow_le_pow_left₀ hg0.le hg 3
  have hn2 : 1≤firstOrderNoiseConstant^2 := by nlinarith
  unfold firstOrderEndpointThreshold
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg3 hΔ) (sq_nonneg s))
      (by positivity : 0≤1342177280*firstOrderNoiseConstant^2*ε^3)).trans
  simp only [one_mul]
  apply div_le_div_of_nonneg_left (by positivity) (pow_pos hε 3)
  nlinarith [pow_pos hε 3]

theorem firstOrderBudgetLinks_le_envelope {Δ ε : ℝ} (hε : 0<ε)
    (hsize : 160*firstOrderOutputScale ε≤Δ) :
    (firstOrderBudgetLinks Δ (firstOrderOutputScale ε):ℝ)≤Δ/ε := by
  have hA := firstOrderOutputScale_pos hε
  have hΔ : 0≤Δ := by linarith
  apply (firstOrderBudgetLinks_lower hA hsize).2.2.trans
  apply div_le_div_of_nonneg_left hΔ hε
  have hg := firstOrderGradientConstant_le_one
  have he := firstOrderOutputScale_separation ε
  nlinarith [mul_le_mul_of_nonneg_left hg hA.le]

end
end SecondOrder
