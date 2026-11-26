import SecondOrder.ScaledFirstOrderModel

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

/-- The coordinate isometry preserves the exact gradient norm; input and
output scaling contribute precisely their scalar factors. -/
theorem scaledFirstOrderPopulation_gradient_norm (Θ : Fin (T+1) → Fin d → Bool)
    (A β : ℝ) (x : Point (FirstOrderDimension d T)) :
    ‖gradient (scaledFirstOrderPopulation Θ A β) x‖=
      |A*β| *‖gradient (firstOrderChain Θ) (firstOrderDilation d T β x)‖ := by
  let U := firstOrderCoordinates d T
  let L := firstOrderDilation d T β
  have hf := (firstOrderChain_contDiff Θ).differentiable (by norm_num)
  have he : fderiv ℝ (scaledFirstOrderPopulation Θ A β) x=
      (A*β) • (fderiv ℝ (firstOrderChain Θ) (L x)).comp U.toLinearIsometry.toContinuousLinearMap := by
    unfold scaledFirstOrderPopulation scalarLinearScaling
    change fderiv ℝ (fun y => A*(firstOrderChain Θ ∘ L) y) x=_
    rw [fderiv_const_mul (hf.comp L.differentiable x) A]
    change A • fderiv ℝ (firstOrderChain Θ ∘ L) x=_
    rw [fderiv_comp x (hf (L x)) L.differentiableAt,L.fderiv]
    ext v
    change A • (fderiv ℝ (firstOrderChain Θ) (L x)) (β • U v)=
      (A*β) • (fderiv ℝ (firstOrderChain Θ) (L x)) (U v)
    rw [map_smul,smul_smul]
  rw [norm_gradient_eq_fderiv,he,
    norm_smul (A*β) ((fderiv ℝ (firstOrderChain Θ) (L x)).comp U.toLinearIsometry.toContinuousLinearMap),Real.norm_eq_abs,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,←norm_gradient_eq_fderiv]

theorem scaledFirstOrderPopulation_gradient_lower (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (x : Point (FirstOrderDimension d T))
    (hu : ∃ j, firstOrderBlockEncoding (Θ j) ((firstOrderDilation d T β x) j)≤1/2) :
    A*β*firstOrderGradientConstant≤‖gradient (scaledFirstOrderPopulation Θ A β) x‖ := by
  rw [scaledFirstOrderPopulation_gradient_norm,abs_of_nonneg (mul_nonneg hA hβ)]
  exact mul_le_mul_of_nonneg_left (firstOrderChain_gradient_lower Θ hd _ hu) (mul_nonneg hA hβ)

theorem scaledFirstOrderPopulation_gradient_progress (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β ε : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) {x : Point (FirstOrderDimension d T)}
    (hx : ‖gradient (scaledFirstOrderPopulation Θ A β) x‖≤ε) :
    firstOrderProgress Θ (firstOrderDilation d T β x)=T+1 := by
  have hp := firstOrderProgress_le Θ (firstOrderDilation d T β x)
  by_contra hn
  have hlow := firstOrderProgress_unfinished_gradient Θ hd (firstOrderDilation d T β x) (by omega)
  have hh := mul_le_mul_of_nonneg_left hlow (mul_nonneg hA hβ)
  rw [scaledFirstOrderPopulation_gradient_norm,abs_of_nonneg (mul_nonneg hA hβ)] at hx
  exact (not_lt_of_ge (hh.trans hx)) hε

theorem scaledFirstOrderPopulation_sosp_progress (Θ : Fin (T+1) → Fin d → Bool)
    (hd : 0<d) {A β ε γ : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) {x : Point (FirstOrderDimension d T)}
    (hx : IsSOSP (scaledFirstOrderPopulation Θ A β) ε γ x) :
    firstOrderProgress Θ (firstOrderDilation d T β x)=T+1 :=
  scaledFirstOrderPopulation_gradient_progress Θ hd hA hβ hε hx.1

end
end SecondOrder
