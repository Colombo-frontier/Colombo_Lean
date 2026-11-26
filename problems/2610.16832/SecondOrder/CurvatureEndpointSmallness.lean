import SecondOrder.CurvatureEndpointDimension

namespace SecondOrder
noncomputable section

/-- One fixed universal smallness constant for all five manuscript-shaped
conditions. Its conservative value makes every later numerical premise explicit. -/
def curvatureEndpointSmallConstant : ℝ :=
  1/(16777216*curvatureGeometryConstant^2*curvatureNoiseConstant^2)

theorem curvatureEndpointSmallConstant_bounds :
    0<curvatureEndpointSmallConstant ∧
      curvatureEndpointSmallConstant*(16384*curvatureNoiseConstant)≤1 ∧
      curvatureEndpointSmallConstant*(8*curvatureGeometryConstant)≤1 ∧
      curvatureEndpointSmallConstant*(16*curvatureGeometryConstant)≤1 ∧
      curvatureEndpointSmallConstant*(256*curvatureGeometryConstant^2)≤1 ∧
      curvatureEndpointSmallConstant*(16384*curvatureGeometryConstant^2)≤1 := by
  norm_num [curvatureEndpointSmallConstant,curvatureGeometryConstant,curvatureNoiseConstant,
    curvatureJetConstant,completionDerivativeBound]

theorem small_condition_scale {c K x y : ℝ} (hK : 0≤K) (hy : 0≤y)
    (hc : c*K≤1) (hx : x≤c*y) : K*x≤y := by
  have h1 := mul_le_mul_of_nonneg_left hx hK
  have h2 := mul_le_mul_of_nonneg_right hc hy
  nlinarith only [h1,h2]

/-- The five conditions have the same shape as the curvature endpoint in
the manuscript. They imply model admissibility, positive stage counts and
the information cap for the chosen actual scales. -/
theorem curvatureEndpoint_smallness (P : Parameters) {σ₀ D γ : ℝ}
    (hσ₀ : 0<σ₀) (hD : 1≤D) (hγ : 0<γ)
    (hLip : γ≤curvatureEndpointSmallConstant*P.gradientLip)
    (hnoise : γ*Real.sqrt D≤curvatureEndpointSmallConstant*curvatureNoiseBudget P)
    (hgrad : curvatureNoiseBudget P*γ*Real.sqrt D≤
      curvatureEndpointSmallConstant*(P.hessianHolder*P.gradientNoise))
    (hvalue : D*(curvatureNoiseBudget P*γ^2+γ^3)≤
      curvatureEndpointSmallConstant*(σ₀*P.hessianHolder^2))
    (hgap : D*γ^3≤curvatureEndpointSmallConstant*(P.gap*P.hessianHolder^2)) :
    64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P ∧
      8*curvatureGeometryConstant*γ≤P.gradientLip ∧
      16*curvatureGeometryConstant*curvatureNoiseBudget P*γ*Real.sqrt D≤P.hessianHolder*P.gradientNoise ∧
      256*curvatureGeometryConstant^2*D*curvatureNoiseBudget P*γ^2≤σ₀*P.hessianHolder^2 ∧
      8*curvatureOutputScale D P.hessianHolder γ≤P.gap ∧
      131072*D≤(curvatureCoefficientScale (curvatureNoiseBudget P) γ)^2 := by
  obtain ⟨_,hcn,hcl,hcg,hcv,hca⟩ := curvatureEndpointSmallConstant_bounds
  have hG := curvatureGeometryConstant_pos
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  have hD0 : 0<D := lt_of_lt_of_le (by norm_num) hD
  have hsqrt : 1≤Real.sqrt D := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hD
  have hσ := curvatureNoiseBudget_pos P
  have hn := small_condition_scale (by positivity : 0≤16384*curvatureNoiseConstant) hσ.le hcn hnoise
  have hl := small_condition_scale (by positivity : 0≤8*curvatureGeometryConstant) P.gradientLip_pos.le hcl hLip
  have hg := small_condition_scale (by positivity : 0≤16*curvatureGeometryConstant)
    (mul_nonneg P.hessianHolder_pos.le P.gradientNoise_pos.le) hcg hgrad
  have hv := small_condition_scale (by positivity : 0≤256*curvatureGeometryConstant^2)
    (mul_nonneg hσ₀.le (sq_nonneg _)) hcv hvalue
  have ha := small_condition_scale (by positivity : 0≤16384*curvatureGeometryConstant^2)
    (mul_nonneg P.gap_pos.le (sq_nonneg _)) hca hgap
  refine ⟨?_,hl,?_,?_,?_,?_⟩
  · have hh : γ≤γ*Real.sqrt D := by nlinarith only [hsqrt,hγ]
    have hmul := mul_le_mul_of_nonneg_left hh (le_of_lt hC)
    have hpos : 0≤curvatureNoiseConstant*γ*Real.sqrt D := by positivity
    nlinarith only [hn,hmul,hpos]
  · nlinarith only [hg]
  · have hpos : 0≤256*curvatureGeometryConstant^2*D*γ^3 := by positivity
    nlinarith only [hv,hpos]
  · have he : 8*curvatureOutputScale D P.hessianHolder γ=
        16384*curvatureGeometryConstant^2*D*γ^3/P.hessianHolder^2 := by
      rw [(curvatureScales_identities hD0 P.hessianHolder_pos hγ).2.2]
      ring
    rw [he]
    exact (div_le_iff₀ (sq_pos_of_pos P.hessianHolder_pos)).2 (by nlinarith only [ha])
  · have hsq := sq_le_sq₀ (by positivity : 0≤16384*curvatureNoiseConstant*(γ*Real.sqrt D)) hσ.le
    have hn2 := hsq.mpr hn
    have hs := Real.sq_sqrt hD0.le
    have hpow : (16384*curvatureNoiseConstant*(γ*Real.sqrt D))^2=
        268435456*curvatureNoiseConstant^2*γ^2*D := by
      calc
        _ = 268435456*curvatureNoiseConstant^2*γ^2*(Real.sqrt D)^2 := by ring
        _ = _ := by rw [hs]
    rw [hpow] at hn2
    unfold curvatureCoefficientScale
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0<32*curvatureNoiseConstant*γ))).2
    have hpos : 0≤curvatureNoiseConstant^2*γ^2*D := by positivity
    nlinarith only [hn2,hpos]

end
end SecondOrder
