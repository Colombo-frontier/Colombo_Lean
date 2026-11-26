import GradientHessian.HigherHierarchyActivationSlices

/-! The actual current-parent force, including the derivative of its
incoming coefficient and the ordered-tail completion-gate coefficient. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem parentExpression_hasGradientAt {R w : ℝ} (hR : 0 < R) (hw : 0 < w)
    (c u : E) (D o T l : ℝ) :
    HasGradientAt (parentExpression R w c D o T l)
      (gradient (Localized.potential R w c) u -
        ((1-Localized.port w c u)*o) • gradient (Localized.incoming R w c) u +
        (T-(D-Localized.incoming R w c u*o)-l) • gradient (Localized.port w c) u) u := by
  have hs := Localized.localized_contDiff hR hw c
  have hV := (hs.1.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt
  have hB := (hs.2.1.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt
  have hp := (hs.2.2.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt
  have hd := (((hV.add (((hasFDerivAt_const (1:ℝ) u).sub hp).mul
    ((hasFDerivAt_const D u).sub (hB.mul_const o)))).add (hp.mul_const T)).sub (hp.const_mul l))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  ext z
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul, InnerProductSpace.toDual_apply,
    inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem localized_port_bounds (w : ℝ) (c u : E) : Localized.port w c u ∈ Set.Icc (0:ℝ) 1 := by
  have hs := Profiles.step_bounds ((‖u-c‖^2-w^2)/(3*w^2))
  unfold Localized.port
  constructor <;> linarith [hs.1,hs.2]

theorem localized_port_gradient_zero (w : ℝ) (c u : E) (h : Localized.port w c u = 0) :
    gradient (Localized.port w c) u = 0 := by
  unfold gradient
  rw [InnerSelector.endpoint_fderiv_zero _ _ (localized_port_bounds w c) (Or.inl h), map_zero]

theorem localized_difference_gradient {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c u : E) :
    gradient (fun x => Localized.potential R w c x-Localized.incoming R w c x) u =
      gradient (Localized.potential R w c) u-gradient (Localized.incoming R w c) u := by
  have hs := Localized.localized_contDiff hR hw c
  simp only [gradient, fderiv_sub (hs.1.differentiable (by norm_num) u)
    (hs.2.1.differentiable (by norm_num) u), map_sub]

end GradientHessian.HigherHierarchy
