import Bilevel.ChiQuadraticLower

/-! A Rayleigh certificate yields the actual operator norm. This adapter
connects the concrete transported matrix quadratic forms to Primitive
smoothness without a dimension factor. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_bilinear_bound (H : E →L[ℝ] E)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) {B : ℝ}
    (hbound : ∀ u,|⟪u,H u⟫|≤B*‖u‖^2) (u v : E) :
    |⟪H u,v⟫|≤B/2*(‖u‖^2+‖v‖^2) := by
  have hpolar : 4*⟪H u,v⟫=⟪u+v,H (u+v)⟫-⟪u-v,H (u-v)⟫ := by
    simp only [map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
    have hc : ⟪v,H u⟫=⟪H u,v⟫ := real_inner_comm _ _
    rw [hc,← hsym u v]
    ring
  have hnorm : ‖u+v‖^2+‖u-v‖^2=2*(‖u‖^2+‖v‖^2) := by
    rw [norm_add_sq_real,norm_sub_sq_real]
    ring
  have hh := (abs_sub ⟪u+v,H (u+v)⟫ ⟪u-v,H (u-v)⟫).trans
    (add_le_add (hbound (u+v)) (hbound (u-v)))
  rw [← hpolar,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4),← mul_add,hnorm] at hh
  nlinarith only [hh]

theorem symmetric_operator_norm (H : E →L[ℝ] E)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ u,|⟪u,H u⟫|≤B*‖u‖^2) : ‖H‖≤B := by
  apply ContinuousLinearMap.opNorm_le_bound H hB
  intro u
  by_cases hu : H u=0
  · rw [hu,norm_zero]
    positivity
  have hh : 0<‖H u‖ := norm_pos_iff.mpr hu
  have hup : 0<‖u‖ := norm_pos_iff.mpr (by intro he; subst u; simp at hu)
  let a := ‖u‖/‖H u‖
  have ha : 0<a := div_pos hup hh
  have hnorm : ‖a • H u‖=‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact div_mul_cancel₀ _ hh.ne'
  have hscale : a*‖H u‖^2=‖u‖*‖H u‖ := by
    dsimp [a]
    field_simp
    ring
  have hb := symmetric_bilinear_bound H hsym hbound u (a • H u)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,abs_of_nonneg (by positivity),hnorm,hscale] at hb
  apply (mul_le_mul_left hup).mp
  nlinarith only [hb]

end Bilevel.ChiQuadratic
