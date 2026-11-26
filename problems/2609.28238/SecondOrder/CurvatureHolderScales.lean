import SecondOrder.CurvatureEndpointQueryLower

namespace SecondOrder
noncomputable section

/-- The manuscript's Hölder scaling with the uniform choice Cν = 2 C₀. -/
def curvatureHolderInputScale (L γ ν : ℝ) : ℝ :=
  (L/(32*curvatureGeometryConstant*γ))^(1/ν)

/-- An auxiliary Lipschitz scale used only to reuse the already proved
coordinate scaling and sequential information identities. -/
def curvatureHolderEffectiveL (L γ ν : ℝ) : ℝ :=
  16*curvatureGeometryConstant*γ*curvatureHolderInputScale L γ ν

theorem curvatureHolderInputScale_pos {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    0<curvatureHolderInputScale L γ ν := by
  have hG := curvatureGeometryConstant_pos
  unfold curvatureHolderInputScale
  exact Real.rpow_pos_of_pos (by positivity) _

theorem curvatureHolderEffectiveL_pos {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    0<curvatureHolderEffectiveL L γ ν := by
  have hG := curvatureGeometryConstant_pos
  unfold curvatureHolderEffectiveL
  exact mul_pos (by positivity) (curvatureHolderInputScale_pos hL hγ)

theorem curvatureHolderInputScale_identity {L γ ν : ℝ} (hγ : 0<γ) :
    curvatureInputScale (curvatureHolderEffectiveL L γ ν) γ=curvatureHolderInputScale L γ ν := by
  unfold curvatureInputScale curvatureHolderEffectiveL
  field_simp [hγ.ne',curvatureGeometryConstant_pos.ne']

theorem curvatureHolderInputScale_power {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) (hν : 0<ν) :
    (curvatureHolderInputScale L γ ν)^ν=L/(32*curvatureGeometryConstant*γ) := by
  have hG := curvatureGeometryConstant_pos
  unfold curvatureHolderInputScale
  rw [←Real.rpow_mul (by positivity),one_div_mul_cancel hν.ne',Real.rpow_one]

/-- A convenient upper bound on the interpolation constant. -/
theorem curvatureInterpolation_scale_bound {C β ν : ℝ} (hC : 0<C) (hβ : 0≤β)
    (hν : 0≤ν) (hν1 : ν≤1) :
    (2*C)^(1-ν)*(C*β)^ν≤2*C*β^ν := by
  calc
    _ ≤ (2*C)^(1-ν)*(2*C*β)^ν := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by nlinarith) hν) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hβ,←mul_assoc,←Real.rpow_add (by positivity)]
      simp only [sub_add_cancel,Real.rpow_one]

theorem curvatureHolderScales_smoothness {D L γ ν : ℝ}
    (hD : 0<D) (hL : 0<L) (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1) :
    let L' := curvatureHolderEffectiveL L γ ν
    let A := curvatureOutputScale D L' γ
    let β := curvatureInputScale L' γ
    (2*(A*β^2*(curvatureGeometryConstant/D)))^(1-ν)*
      (A*β^3*(curvatureGeometryConstant/D))^ν≤L/2 := by
  have hG := curvatureGeometryConstant_pos
  dsimp only
  have hL' := curvatureHolderEffectiveL_pos (ν := ν) hL hγ
  have hs := curvatureScales_smoothness hD hL' hγ
  rw [hs.1,hs.2,curvatureHolderEffectiveL]
  have he : 16*curvatureGeometryConstant*γ*curvatureHolderInputScale L γ ν/2=
      (8*curvatureGeometryConstant*γ)*curvatureHolderInputScale L γ ν := by ring
  rw [he]
  apply (curvatureInterpolation_scale_bound (by positivity)
    (curvatureHolderInputScale_pos hL hγ).le hν.le hν1).trans_eq
  rw [curvatureHolderInputScale_power hL hγ hν]
  field_simp [hγ.ne',curvatureGeometryConstant_pos.ne']
  <;> ring

theorem curvatureHolderScales_gradient_noise {D L σ γ ν : ℝ}
    (hD : 0<D) (hL : 0<L) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤σ) :
    let L' := curvatureHolderEffectiveL L γ ν
    curvatureOutputScale D L' γ*curvatureInputScale L' γ*
      (curvatureNoiseConstant*(curvatureCoefficientScale σ γ+1)/Real.sqrt D)≤
        σ*Real.sqrt D/curvatureHolderInputScale L γ ν := by
  have hG := curvatureGeometryConstant_pos
  dsimp only
  apply (curvatureScales_gradient_noise hD (curvatureHolderEffectiveL_pos hL hγ) hγ hsmall).trans_eq
  have hβ := curvatureHolderInputScale_pos (ν := ν) hL hγ
  unfold curvatureHolderEffectiveL
  field_simp [hγ.ne',hG.ne',hβ.ne']
  <;> ring

end
end SecondOrder

