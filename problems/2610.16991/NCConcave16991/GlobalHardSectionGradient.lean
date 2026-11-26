import NCConcave16991.GlobalHardStateGradient

/-! # Gradient control on actual isometric affine sections -/

namespace NCConcave16991.GlobalHard

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem norm_gradient_eq_fderiv (f : E → ℝ) (s : E) : ‖gradient f s‖ = ‖fderiv ℝ f s‖ := by
  have hh := (InnerProductSpace.toDual ℝ E).norm_map (gradient f s)
  rw [toDual_gradient] at hh
  exact hh.symm

/-- A coordinate section inherits the actual ambient gradient bound. -/
theorem isometric_section_gradient_le (f : E → ℝ) (g : F → ℝ) (L : E →ₗᵢ[ℝ] F)
    (s : E) (x : F) (c : ℝ) (hg : DifferentiableAt ℝ g x)
    (heq : ∀ t, g (x + L (t - s)) = f t + c) :
    ‖gradient f s‖ ≤ ‖gradient g x‖ := by
  have ha : HasFDerivAt (fun t : E ↦ x + L (t - s)) L.toContinuousLinearMap s := by
    exact ((L.toContinuousLinearMap.hasFDerivAt.comp s ((hasFDerivAt_id s).sub_const s)).const_add x).congr_fderiv (by simp)
  have hgg : HasFDerivAt g (fderiv ℝ g x) (x + L (s - s)) := by
    simpa using hg.hasFDerivAt
  have hc := hgg.comp s ha
  have hfun : (g ∘ fun t : E ↦ x + L (t - s)) = fun t ↦ f t + c := funext heq
  rw [hfun] at hc
  have hf : HasFDerivAt f ((fderiv ℝ g x).comp L.toContinuousLinearMap) s := by
    convert hc.sub_const c using 1
    funext t
    simp
  have hL : ‖L.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound L.toContinuousLinearMap (by norm_num)
    intro t
    simp
  rw [norm_gradient_eq_fderiv, norm_gradient_eq_fderiv, hf.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left hL (norm_nonneg _)).trans_eq (mul_one _))

end
end NCConcave16991.GlobalHard
