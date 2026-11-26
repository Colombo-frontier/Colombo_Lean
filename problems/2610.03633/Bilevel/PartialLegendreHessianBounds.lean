import Bilevel.PartialLegendreDerivative
import Bilevel.PartialLegendreStrongConvex

/-! Both sharp lower-block Hessian inequalities for the actual conjugate.
Symmetry/coercivity are consequences of the scalar potential and gradient
model, rather than independent Hessian certificates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G)
  (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
include hP

theorem solution_strong_monotone :
    FrozenTilt.StrongMonotone (solution hδ hG) (1/(1+(δ:ℝ))) := by
  intro u v
  have h1 := conjugate_strong_model hδ hG P hP u v
  have h2 := conjugate_strong_model hδ hG P hP v u
  rw [norm_sub_rev v u] at h1
  have hi : ⟪solution hδ hG u,v-u⟫+⟪solution hδ hG v,u-v⟫ =
      -⟪solution hδ hG u-solution hδ hG v,u-v⟫ := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,inner_sub_right]
    ring
  have hs := add_le_add h1 h2
  rw [show conjugate hδ hG P u+⟪solution hδ hG u,v-u⟫+
      1/(2*(1+(δ:ℝ)))*‖u-v‖^2 +
      (conjugate hδ hG P v+⟪solution hδ hG v,u-v⟫+
        1/(2*(1+(δ:ℝ)))*‖u-v‖^2) =
      conjugate hδ hG P u+conjugate hδ hG P v+
        (⟪solution hδ hG u,v-u⟫+⟪solution hδ hG v,u-v⟫)+
          1/(1+(δ:ℝ))*‖u-v‖^2 by field_simp; ring,hi] at hs
  linarith

theorem conjugate_hessian_lower (y : E) (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ))
    (hDG : HasFDerivAt G B (solution hδ hG y)) (v : E) :
    1/(1+(δ:ℝ))*‖v‖^2 ≤ ⟪(linearEquiv hδ B hB).symm v,v⟫ :=
  FrozenTilt.derivative_coercive (solution_strong_monotone hδ hG P hP)
    y ((linearEquiv hδ B hB).symm : E →L[ℝ] E)
    (solution_hasFDerivAt hδ hG y B hB hDG) v

omit hP in
theorem conjugate_hessian_upper (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) (v : E) :
    ⟪(linearEquiv hδ B hB).symm v,v⟫ ≤ 1/(1-(δ:ℝ))*‖v‖^2 := by
  have hn : ‖⟪(linearEquiv hδ B hB).symm v,v⟫‖ ≤ ‖(linearEquiv hδ B hB).symm v‖*‖v‖ :=
    norm_inner_le_norm _ _
  have hv := (((linearEquiv hδ B hB).symm : E →L[ℝ] E).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (linearEquiv_inverse_bound hδ B hB) (norm_nonneg v))
  exact (le_abs_self _).trans (hn.trans (by
    convert mul_le_mul_of_nonneg_right hv (norm_nonneg v) using 1
    ring))

theorem actual_conjugate_hessian_bounds (y : E) (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ))
    (hDG : HasFDerivAt G B (solution hδ hG y)) :
    HasFDerivAt (gradient (conjugate hδ hG P)) ((linearEquiv hδ B hB).symm : E →L[ℝ] E) y ∧
      ∀ v, 1/(1+(δ:ℝ))*‖v‖^2 ≤ ⟪(linearEquiv hδ B hB).symm v,v⟫ ∧
        ⟪(linearEquiv hδ B hB).symm v,v⟫ ≤ 1/(1-(δ:ℝ))*‖v‖^2 :=
  ⟨conjugate_gradient_hasFDerivAt hδ hG P hP y B hB hDG,
    fun v => ⟨conjugate_hessian_lower hδ hG P hP y B hB hDG v,
      conjugate_hessian_upper hδ B hB v⟩⟩

end Bilevel.PartialLegendre
