import SampleReuse.RadialExterior
import SampleReuse.TangentCurvature

open scoped Topology InnerProductSpace

namespace SampleReuse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem scalar_norm_tangent_hessian {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x : E} (hx : x ≠ 0) (w : E) (hw : ⟪x,w⟫_ℝ = 0) :
    ⟪fderiv ℝ (gradient (fun y : E => f ‖y‖)) x w,w⟫_ℝ =
      (deriv f ‖x‖/‖x‖)*‖w‖^2 := by
  let a : ℝ → ℝ := fun r => deriv f r/r
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hdf : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1:WithTop ℕ∞)+1) f from hf)).2.2
  have ha : DifferentiableAt ℝ a ‖x‖ :=
    ((hdf.differentiable (by norm_num)) ‖x‖).div (differentiableAt_id) hr
  have hd := (ha.hasDerivAt.comp_hasFDerivAt x (norm_hasFDerivAt_inner hx)).smul
    (hasFDerivAt_id x)
  simp only [Function.comp_def,id_eq] at hd
  have he : gradient (fun y : E => f ‖y‖) =ᶠ[𝓝 x] (fun y => a ‖y‖ • y) := by
    have hy : ∀ᶠ y : E in 𝓝 x, 0 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (norm_pos_iff.mpr hx))
    filter_upwards [hy] with y hy
    exact (scalar_norm_hasGradientAt (norm_pos_iff.mp hy)
      ((hf.differentiable (by norm_num)) ‖y‖).hasDerivAt).gradient
  rw [he.fderiv_eq, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply,smul_eq_mul,hw,mul_zero,zero_smul,add_zero,real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  rfl

theorem radialWallLoss_tangent_hessian (b : ℝ) {R : ℝ} (hR : 0 < R)
    {x : E} (hx : x ≠ 0) (w : E) (hw : ⟪x,w⟫_ℝ = 0) :
    ⟪fderiv ℝ (gradient (radialWallLoss b R)) x w,w⟫_ℝ =
      (b*radialRise (‖x‖/R)/‖x‖)*‖w‖^2 := by
  change ⟪fderiv ℝ (gradient (fun y : E => radialWall b R ‖y‖)) x w,w⟫_ℝ = _
  rw [scalar_norm_tangent_hessian (radialWall_contDiff b R 2) hx w hw,
    (radialWall_hasDerivAt b hR ‖x‖).deriv]

theorem radialWallLoss_tangent_bound {b R : ℝ} (hb : 0 ≤ b) (hR : 0 < R)
    {x : E} (hx : R/2 ≤ ‖x‖) (w : E) (hw : ⟪x,w⟫_ℝ = 0) :
    ⟪fderiv ℝ (gradient (radialWallLoss b R)) x w,w⟫_ℝ ≤
      (2*b/R)*‖w‖^2 := by
  have hr : 0 < ‖x‖ := (half_pos hR).trans_le hx
  rw [radialWallLoss_tangent_hessian b hR (norm_pos_iff.mp hr) w hw]
  have hS := radialRise_mem (‖x‖/R)
  have hm : b*radialRise (‖x‖/R)/‖x‖ ≤ b/‖x‖ :=
    div_le_div_of_nonneg_right (mul_le_of_le_one_right hb hS.2) hr.le
  have hh : b/‖x‖ ≤ 2*b/R := (div_le_div_iff₀ hr hR).mpr (by
    have hp := mul_nonneg hb (show 0 ≤ 2*‖x‖-R by linarith)
    nlinarith only [hp])
  exact mul_le_mul_of_nonneg_right (hm.trans hh) (sq_nonneg _)

end
end SampleReuse
