import SecondOrder.DimensionJets
import SecondOrder.BlockMixtureInterior

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_const_mul_scalar {f : E → ℝ} (hf : Differentiable ℝ f) (c : ℝ) :
    gradient (fun y => c*f y) = fun y => c • gradient f y := by
  funext y
  simp only [gradient, fderiv_const_mul (hf y), map_smul]

theorem hessian_const_mul_scalar {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (gradient (fun y => c*f y)) x = c • fderiv ℝ (gradient f) x := by
  rw [gradient_const_mul_scalar (hf.differentiable (by norm_num))]
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact fderiv_const_smul (hg.differentiable (by norm_num) x) c

theorem gradient_add_scalar {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    gradient (fun y => f y+g y) = fun y => gradient f y+gradient g y := by
  funext y
  simp only [gradient, fderiv_add (hf y) (hg y), map_add]

theorem hessian_add_scalar {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (gradient (fun y => f y+g y)) x =
      fderiv ℝ (gradient f) x+fderiv ℝ (gradient g) x := by
  rw [gradient_add_scalar (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  have hgf : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hgg : ContDiff ℝ 1 (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hg.fderiv_right (by norm_num))
  exact fderiv_add (hgf.differentiable (by norm_num) x) (hgg.differentiable (by norm_num) x)

theorem gradient_linear_contraction (f : F → ℝ) (hf : ContDiff ℝ 2 f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (x : E) :
    ‖gradient (f ∘ L) x‖ ≤ ‖gradient f (L x)‖ := by
  simp only [norm_gradient_eq_fderiv, ← norm_first_iteratedFDeriv]
  exact iteratedFDeriv_linear_contraction f L hL 1 (hf.of_le (by norm_num)) x

theorem hessian_linear_contraction (f : F → ℝ) (hf : ContDiff ℝ 2 f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (x : E) :
    ‖fderiv ℝ (gradient (f ∘ L)) x‖ ≤ ‖fderiv ℝ (gradient f) (L x)‖ := by
  simp only [norm_fderiv_gradient]
  exact iteratedFDeriv_linear_contraction f L hL 2 hf x

end
end SecondOrder
