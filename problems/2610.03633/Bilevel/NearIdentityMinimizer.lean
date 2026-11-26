import Bilevel.NearIdentityInverse
import Bilevel.JointDerivative

/-! Actual quadratic-plus-perturbation objective and unique minimizer.
The Taylor lower bound is derived from the actual Lipschitz gradient. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A genuine uniform derivative/Hessian budget supplies the Lipschitz premise
used by the homotopy construction. -/
theorem gradient_lipschitz_of_derivative_bound {δ : NNReal} {G : E → E}
    (DG : E → E →L[ℝ] E) (hDG : ∀ z,HasFDerivAt G (DG z) z)
    (hbound : ∀ z,‖DG z‖≤(δ:ℝ)) : LipschitzWith δ G := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hDG z).differentiableAt)
  intro z
  rw [(hDG z).fderiv]
  exact_mod_cast hbound z

def objective (P : E → ℝ) (u : E) (t : Time) (z : E) : ℝ :=
  ‖z‖^2/2 + (t:ℝ)*P z - ⟪u,z⟫

theorem objective_growth_of_equation {δ : NNReal} {G : E → E} (P : E → ℝ)
    (hP : ∀ z, HasGradientAt P (G z) z) (hG : LipschitzWith δ G)
    (u z y : E) (t : Time) (heq : z+(t:ℝ) • G z=u) :
    (1-(δ:ℝ))/2 * ‖y-z‖^2 ≤ objective P u t y-objective P u t z := by
  have hlip : ∀ x y, ‖G x-G y‖ ≤ (δ:ℝ)*‖x-y‖ := by
    intro x y
    simpa only [dist_eq_norm] using hG.dist_le_mul x y
  have htaylor := JointDerivative.gradient_taylor P G (δ:ℝ) hP hlip z (y-z)
  rw [add_sub_cancel, Real.norm_eq_abs] at htaylor
  have hlow := (abs_le.mp htaylor).1
  have htlow := mul_le_mul_of_nonneg_left hlow t.property.1
  have hn : ‖y‖^2-‖z‖^2-2*⟪z,y-z⟫ = ‖y-z‖^2 := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm y z]
    ring
  have hu : ⟪u,y⟫-⟪u,z⟫ = ⟪z,y-z⟫+(t:ℝ)*⟪G z,y-z⟫ := by
    rw [← inner_sub_right, ← heq, inner_add_left, real_inner_smul_left]
  have hδt := mul_le_mul_of_nonneg_right t.property.2
    (mul_nonneg δ.coe_nonneg (sq_nonneg ‖y-z‖))
  unfold objective
  nlinarith

theorem inverse_minimizes {δ : NNReal} (hδ : δ < 1) {G : E → E} (P : E → ℝ)
    (hP : ∀ z, HasGradientAt P (G z) z) (hG : LipschitzWith δ G)
    (u y : E) (t : Time) :
    objective P u t (inverse hδ hG u t) ≤ objective P u t y := by
  have h := objective_growth_of_equation P hP hG u (inverse hδ hG u t) y t
    (inverse_equation hδ hG u t)
  have hp : 0 ≤ (1-(δ:ℝ))/2*‖y-inverse hδ hG u t‖^2 := by
    have hd : 0<1-(δ:ℝ) := sub_pos.mpr hδ
    positivity
  linarith

theorem inverse_unique_minimizer {δ : NNReal} (hδ : δ < 1) {G : E → E} (P : E → ℝ)
    (hP : ∀ z, HasGradientAt P (G z) z) (hG : LipschitzWith δ G)
    (u y : E) (t : Time) :
    (∀ z, objective P u t y ≤ objective P u t z) ↔ y=inverse hδ hG u t := by
  constructor
  · intro hy
    have h := objective_growth_of_equation P hP hG u (inverse hδ hG u t) y t
      (inverse_equation hδ hG u t)
    have hy' := hy (inverse hδ hG u t)
    have hd : 0<1-(δ:ℝ) := sub_pos.mpr hδ
    have hp : 0 < (1-(δ:ℝ))/2 := by positivity
    have hn : ‖y-inverse hδ hG u t‖^2 = 0 := by nlinarith [sq_nonneg ‖y-inverse hδ hG u t‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro hy z
    rw [hy]
    exact inverse_minimizes hδ P hP hG u z t

end Bilevel.NearIdentityInverse
