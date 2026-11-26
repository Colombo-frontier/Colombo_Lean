import SampleReuse.Model

open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tangentPart (e u : E) : E := u - ⟪u,e⟫_ℝ • e

theorem tangentPart_orthogonal {e u : E} (he : ‖e‖=1) :
    ⟪tangentPart e u,e⟫_ℝ = 0 := by
  simp [tangentPart, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]

theorem tangentPart_norm_sq {e u : E} (he : ‖e‖=1) :
    ‖tangentPart e u‖^2 = ‖u‖^2 - ⟪u,e⟫_ℝ^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [tangentPart, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm e u,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
  ring

theorem tangentPart_norm_le {e u : E} (he : ‖e‖=1) :
    ‖tangentPart e u‖ ≤ ‖u‖ := by
  have hh := tangentPart_norm_sq (u := u) he
  nlinarith [sq_nonneg ⟪u,e⟫_ℝ, norm_nonneg (tangentPart e u), norm_nonneg u]

theorem tangentPart_distance {e u : E} (he : ‖e‖=1) :
    ‖tangentPart e u-u‖ = |⟪u,e⟫_ℝ| := by
  simp [tangentPart, sub_sub_cancel_left, norm_smul, he, Real.norm_eq_abs]

theorem quadratic_direction_difference (H : E →L[ℝ] E) (u w : E) :
    |⟪H w,w⟫_ℝ-⟪H u,u⟫_ℝ| ≤ ‖H‖*‖w-u‖*(‖w‖+‖u‖) := by
  have hid : ⟪H w,w⟫_ℝ-⟪H u,u⟫_ℝ =
      ⟪H (w-u),w⟫_ℝ+⟪H u,w-u⟫_ℝ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |⟪H (w-u),w⟫_ℝ|+|⟪H u,w-u⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖H (w-u)‖*‖w‖+‖H u‖*‖w-u‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖H‖*‖w-u‖)*‖w‖+(‖H‖*‖u‖)*‖w-u‖ := add_le_add
      (mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _))
    _ = _ := by ring

/-- Projecting a unit hidden direction onto the sphere tangent space costs
at most twice its radial component times the true Hessian operator norm. -/
theorem tangentPart_quadratic_le (H : E →L[ℝ] E) {e u : E}
    (he : ‖e‖=1) (hu : ‖u‖=1) :
    ⟪H (tangentPart e u),tangentPart e u⟫_ℝ ≤
      ⟪H u,u⟫_ℝ + 2*‖H‖*|⟪u,e⟫_ℝ| := by
  have hd := quadratic_direction_difference H u (tangentPart e u)
  rw [tangentPart_distance he, hu] at hd
  have ht : ‖tangentPart e u‖ ≤ 1 := (tangentPart_norm_le he).trans_eq hu
  have hm := mul_le_mul_of_nonneg_left (show ‖tangentPart e u‖+1 ≤ 2 by linarith)
    (mul_nonneg (norm_nonneg H) (abs_nonneg ⟪u,e⟫_ℝ))
  have hh := (le_abs_self _).trans (hd.trans hm)
  nlinarith only [hh]

theorem tangentPart_retains_negative (H W : E →L[ℝ] E) {e u : E}
    (he : ‖e‖=1) (hu : ‖u‖=1) {γ : ℝ} (hγ : 0 < γ)
    (hcurv : ⟪H u,u⟫_ℝ ≤ -8*γ)
    (herror : 2*‖H‖*|⟪u,e⟫_ℝ| ≤ γ)
    (hwall : ⟪W (tangentPart e u),tangentPart e u⟫_ℝ ≤ γ*‖tangentPart e u‖^2) :
    tangentPart e u ≠ 0 ∧
      ⟪(H+W) (tangentPart e u),tangentPart e u⟫_ℝ < -γ*‖tangentPart e u‖^2 := by
  have ht : ‖tangentPart e u‖ ≤ 1 := (tangentPart_norm_le he).trans_eq hu
  have ht0 := norm_nonneg (tangentPart e u)
  have hs : ‖tangentPart e u‖^2 ≤ 1 := by nlinarith only [ht, ht0]
  have hc := tangentPart_quadratic_le H he hu
  have hneg : ⟪(H+W) (tangentPart e u),tangentPart e u⟫_ℝ ≤ -6*γ := by
    simp only [ContinuousLinearMap.add_apply, inner_add_left]
    have hm := mul_le_mul_of_nonneg_left hs hγ.le
    nlinarith only [hc, hcurv, herror, hwall, hm]
  constructor
  · intro hzero
    simp only [hzero, map_zero, inner_zero_left] at hneg
    linarith
  · have hm := mul_le_mul_of_nonneg_left hs hγ.le
    linarith

end
end SampleReuse
