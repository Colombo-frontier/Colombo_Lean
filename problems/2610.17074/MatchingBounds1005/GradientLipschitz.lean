import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-! A global Hessian operator bound controls the actual Euclidean gradient. -/
noncomputable section
open Set
open scoped ContDiff

namespace MatchingBounds1005
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_lipschitz_of_hessian_bound {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    {b : ℝ} (hbound : ∀ x : E, ‖iteratedFDeriv ℝ 2 F x‖ ≤ b) (x y : E) :
    ‖gradient F y - gradient F x‖ ≤ b * ‖y - x‖ := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp hF).2).1
  have hnorm (z : E) : ‖fderiv ℝ (fderiv ℝ F) z‖ = ‖iteratedFDeriv ℝ 2 F z‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1),
      ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
  have h := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z _ => (hnorm z).trans_le (hbound z)) (mem_univ x) (mem_univ y)
  change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) -
      (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F x)‖ ≤ _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact h

end MatchingBounds1005
