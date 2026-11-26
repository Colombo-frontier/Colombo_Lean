import SampleReuse.RadialTangent
import SampleReuse.RadialAdmissible
import SampleReuse.CurvatureJet

open SecondOrder
open scoped Topology InnerProductSpace

namespace SampleReuse
noncomputable section

variable {d : ℕ}

theorem radialGlobalization_hessian_inside {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) {x : Point d} (hx : ‖x‖ < R) :
    hessian (radialGlobalization f b R) x = hessian f x+hessian (radialWallLoss b R) x := by
  have hw := radialWallLoss_contDiff (E := Point d) b hR 2
  have hg := ((radialCutoffLoss_contDiff (E := Point d) hR 2).mul hf).add hw
  have he : radialGlobalization f b R =ᶠ[𝓝 x] (fun y => f y+radialWallLoss b R y) := by
    have hy : ∀ᶠ y : Point d in 𝓝 x, ‖y‖ < R :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
    filter_upwards [hy] with y hy
    have hc := radialCutoff_one ((div_le_one hR).mpr hy.le)
    simp only [radialGlobalization,radialCutoffLoss,hc,one_mul]
  have hj : ScalarJetEq (radialGlobalization f b R) (fun y => f y+radialWallLoss b R y) x :=
    ⟨hg,hf.add hw,he.eq_of_nhds,he.fderiv_eq,he.fderiv.fderiv_eq⟩
  change fderiv ℝ (gradient (radialGlobalization f b R)) x =
    fderiv ℝ (gradient f) x+fderiv ℝ (gradient (radialWallLoss b R)) x
  rw [hj.hessian_eq]
  exact hessian_add_scalar hf hw x

theorem radialGlobalization_hessian_core {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (b : ℝ) {R : ℝ} (hR : 0 < R) {x : Point d} (hx : ‖x‖ < R/2) :
    hessian (radialGlobalization f b R) x = hessian f x := by
  have hg := ((radialCutoffLoss_contDiff (E := Point d) hR 2).mul hf).add
    (radialWallLoss_contDiff b hR 2)
  have he : radialGlobalization f b R =ᶠ[𝓝 x] f := by
    have hy : ∀ᶠ y : Point d in 𝓝 x, ‖y‖ < R/2 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
    filter_upwards [hy] with y hy
    have hc := radialCutoff_one ((div_le_one hR).mpr (by linarith : ‖y‖ ≤ R))
    have hw := radialWall_zero b hR hy.le
    simp only [radialGlobalization,radialCutoffLoss,radialWallLoss,hc,hw,one_mul,add_zero]
  exact (show ScalarJetEq (radialGlobalization f b R) f x from
    ⟨hg,hf,he.eq_of_nhds,he.fderiv_eq,he.fderiv.fderiv_eq⟩).hessian_eq

/-- The radial wall cannot remove sufficiently transverse negative curvature
in the transition annulus. The Hessian in this statement is the actual one. -/
theorem radialGlobalization_annulus_not_sosp {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    {b R ε γ : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (hwall : 2*b/R ≤ γ) {x : Point d} (hxlo : R/2 ≤ ‖x‖) (hxhi : ‖x‖ < R)
    (u : Point d) (hu : ‖u‖=1)
    (hcurv : ⟪hessian f x u,u⟫_ℝ ≤ -8*γ)
    (herror : 2*‖hessian f x‖*|⟪u,radialUnit x⟫_ℝ| ≤ γ) :
    ¬ IsSOSP (radialGlobalization f b R) ε γ x := by
  have hr : 0 < ‖x‖ := (half_pos hR).trans_le hxlo
  have hxn := norm_pos_iff.mp hr
  let w := tangentPart (radialUnit x) u
  have he := radialUnit_norm hxn
  have ht : ⟪x,w⟫_ℝ=0 := by
    have ho := tangentPart_orthogonal (u := u) he
    have hrepr : x = ‖x‖ • radialUnit x := by
      simp only [radialUnit, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have ho' : ⟪radialUnit x,w⟫_ℝ=0 := (real_inner_comm _ _).trans ho
    rw [hrepr,real_inner_smul_left,ho',mul_zero]
  have hw : ⟪hessian (radialWallLoss b R) x w,w⟫_ℝ ≤ γ*‖w‖^2 :=
    (radialWallLoss_tangent_bound hb hR hxlo w ht).trans
      (mul_le_mul_of_nonneg_right hwall (sq_nonneg _))
  have hn := (tangentPart_retains_negative (hessian f x) (hessian (radialWallLoss b R) x)
    he hu hγ hcurv herror hw).2
  intro hs
  have hh := hs.2 w
  have hH := radialGlobalization_hessian_inside hf b hR hxhi
  change -γ*‖w‖^2 ≤ ⟪hessian (radialGlobalization f b R) x w,w⟫_ℝ at hh
  rw [hH] at hh
  exact (not_lt_of_ge hh) hn

theorem radialGlobalization_core_not_sosp {f : Point d → ℝ} (hf : ContDiff ℝ 2 f)
    (b : ℝ) {R ε γ : ℝ} (hR : 0 < R) (hγ : 0 < γ) {x : Point d} (hx : ‖x‖ < R/2)
    (u : Point d) (hu : ‖u‖=1) (hcurv : ⟪hessian f x u,u⟫_ℝ ≤ -8*γ) :
    ¬ IsSOSP (radialGlobalization f b R) ε γ x := by
  intro hs
  have hh := hs.2 u
  change -γ*‖u‖^2 ≤ ⟪hessian (radialGlobalization f b R) x u,u⟫_ℝ at hh
  rw [radialGlobalization_hessian_core hf b hR hx,hu] at hh
  norm_num only [one_pow,mul_one] at hh
  linarith

end
end SampleReuse
