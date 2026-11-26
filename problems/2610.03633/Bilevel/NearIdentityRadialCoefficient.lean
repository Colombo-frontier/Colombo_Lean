import Bilevel.RadialWrapper

/-! The total radial coefficient is tested by the actual derivative of the
gradient along a unit direction orthogonal to the whole frame and the point.
This includes hidden wrapper contributions, not just the public radial term. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityConfinement

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem transverse_radial_coefficient
    (G : E → E) (U : F →L[ℝ] E) (a : E → F) (γ : E → ℝ) (p e : E)
    (DG : E →L[ℝ] E) (Dγ : E →L[ℝ] ℝ)
    (hDG : HasFDerivAt G DG p) (hDγ : HasFDerivAt γ Dγ p)
    (hdecomp : ∀ x,G x=U (a x)+γ x • x)
    (heU : ∀ w,⟪e,U w⟫=0) (hep : ⟪e,p⟫=0) (he : ‖e‖=1) :
    ⟪e,DG e⟫=γ p := by
  have hfun : (fun x => ⟪e,G x⟫)=(fun x => γ x*⟪e,x⟫) := by
    funext x
    rw [hdecomp x, inner_add_right, heU, real_inner_smul_right, zero_add]
  have hl := (innerSL ℝ e).hasFDerivAt.comp p hDG
  have hr := hDγ.mul (innerSL ℝ e).hasFDerivAt
  change HasFDerivAt (fun x => ⟪e,G x⟫) ((innerSL ℝ e).comp DG) p at hl
  change HasFDerivAt (fun x => γ x*⟪e,x⟫) _ p at hr
  rw [hfun] at hl
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L e) (hl.unique hr)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply',
    innerSL_apply, smul_eq_mul, hep, real_inner_self_eq_norm_sq, he,
    one_pow, mul_one, zero_mul, add_zero, zero_add] using hd

theorem total_radial_coefficient_bound
    (G : E → E) (U : F →L[ℝ] E) (a : E → F) (γ : E → ℝ) (p e : E)
    (DG : E →L[ℝ] E) (Dγ : E →L[ℝ] ℝ)
    (hDG : HasFDerivAt G DG p) (hDγ : HasFDerivAt γ Dγ p)
    (hdecomp : ∀ x,G x=U (a x)+γ x • x)
    (heU : ∀ w,⟪e,U w⟫=0) (hep : ⟪e,p⟫=0) (he : ‖e‖=1)
    {δ : ℝ} (hbound : ‖DG‖≤δ) : |γ p|≤δ := by
  rw [← transverse_radial_coefficient G U a γ p e DG Dγ hDG hDγ hdecomp heU hep he]
  have hi := abs_real_inner_le_norm e (DG e)
  have hn := DG.le_opNorm e
  rw [he, one_mul] at hi
  rw [he, mul_one] at hn
  exact hi.trans (hn.trans hbound)

end Bilevel.NearIdentityConfinement
