import SecondOrder.FirstOrderEndpointDimension
import SecondOrder.CurvatureEndpointSmallness

namespace SecondOrder
noncomputable section

def firstOrderEndpointSmallConstant : ℝ :=
  firstOrderGradientConstant/(65536*firstOrderNoiseConstant*firstOrderGeometryConstant)

theorem firstOrderEndpointSmallConstant_bounds :
    0<firstOrderEndpointSmallConstant ∧
      firstOrderEndpointSmallConstant*(2048*firstOrderNoiseConstant/firstOrderGradientConstant)≤1 ∧
      firstOrderEndpointSmallConstant*(4*firstOrderGeometryConstant/firstOrderGradientConstant)≤1 ∧
      firstOrderEndpointSmallConstant*(640/firstOrderGradientConstant)≤1 := by
  have hg := firstOrderGradientConstant_pos
  have hn := firstOrderNoiseConstant_pos
  have hG := firstOrderGeometryConstant_pos
  refine ⟨by unfold firstOrderEndpointSmallConstant; positivity,?_,?_,?_⟩
  all_goals
    unfold firstOrderEndpointSmallConstant
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (by positivity)).2
    norm_num [firstOrderNoiseConstant,firstOrderGeometryConstant,firstOrderJetConstant,completionDerivativeBound]
    nlinarith only [hg]

/-- The three manuscript-shaped conditions imply all actual scale, gap,
noise, and information-cap inequalities, including integer rounding. -/
theorem firstOrderEndpoint_smallness (P : Parameters) {σ₀ D ε : ℝ}
    (hσ₀ : 0<σ₀) (hD : 0≤D) (hε : 0<ε)
    (hLip : ε≤firstOrderEndpointSmallConstant*P.gradientLip)
    (hnoise : ε≤firstOrderEndpointSmallConstant*firstOrderNoiseBudget P σ₀)
    (hHolder : ε*Real.sqrt D≤firstOrderEndpointSmallConstant*P.hessianHolder)
    (hgap : ε≤firstOrderEndpointSmallConstant*P.gap) :
    4*firstOrderNoiseConstant*firstOrderOutputScale ε≤firstOrderNoiseBudget P σ₀ ∧
      firstOrderOutputScale ε*firstOrderGeometryConstant≤P.gradientLip ∧
      firstOrderOutputScale ε*(firstOrderGeometryConstant*Real.sqrt D)≤P.hessianHolder ∧
      160*firstOrderOutputScale ε≤P.gap ∧
      32768≤(firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε))^2 := by
  obtain ⟨_,hcn,hcl,hca⟩ := firstOrderEndpointSmallConstant_bounds
  have hg := firstOrderGradientConstant_pos
  have hn := firstOrderNoiseConstant_pos
  have hG := firstOrderGeometryConstant_pos
  have hA := firstOrderOutputScale_pos hε
  have hs := firstOrderNoiseBudget_pos P hσ₀
  have hnoise' := small_condition_scale (by positivity : 0≤2048*firstOrderNoiseConstant/firstOrderGradientConstant)
    hs.le hcn hnoise
  have hLip' := small_condition_scale (by positivity : 0≤4*firstOrderGeometryConstant/firstOrderGradientConstant)
    P.gradientLip_pos.le hcl hLip
  have hHolder' := small_condition_scale (by positivity : 0≤4*firstOrderGeometryConstant/firstOrderGradientConstant)
    P.hessianHolder_pos.le hcl hHolder
  have hgap' := small_condition_scale (by positivity : 0≤640/firstOrderGradientConstant)
    P.gap_pos.le hca hgap
  have he : 512*firstOrderNoiseConstant*firstOrderOutputScale ε≤firstOrderNoiseBudget P σ₀ := by
    convert hnoise' using 1 <;> unfold firstOrderOutputScale <;> ring
  refine ⟨?_,?_,?_,?_,?_⟩
  · nlinarith [mul_pos hn hA]
  · convert hLip' using 1 <;> unfold firstOrderOutputScale <;> ring
  · convert hHolder' using 1 <;> unfold firstOrderOutputScale <;> ring
  · convert hgap' using 1 <;> unfold firstOrderOutputScale <;> ring
  · have hR : 256≤firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε) := by
      apply (le_div_iff₀ (by positivity : 0<2*firstOrderNoiseConstant*firstOrderOutputScale ε)).2
      nlinarith only [he]
    nlinarith [sq_nonneg (firstOrderCoefficientScale (firstOrderNoiseBudget P σ₀) (firstOrderOutputScale ε)-256)]

end
end SecondOrder
