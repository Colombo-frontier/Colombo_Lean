import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Taylor estimates with constants independent of the Hessian norm.
The first estimate uses the actual Lipschitz derivative and a convex-ball
mean-value argument. Its slightly larger absolute constant is sufficient
for the NALEN convergence proof. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric
open scoped NNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem first_taylor_remainder {f : E → F} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) (x y : E) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ (L : ℝ)*‖y-x‖^2 := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (𝕜 := ℝ) (f := f) (s := closedBall x ‖y-x‖) (φ := fderiv ℝ f x)
    (C := (L : ℝ)*‖y-x‖) (fun z _ => hf z) (fun z hz => ?_)
    (convex_closedBall x ‖y-x‖) (mem_closedBall_self (norm_nonneg _))
    (show y ∈ closedBall x ‖y-x‖ by simp [mem_closedBall,dist_eq_norm])
  · simpa only [pow_two,mul_assoc] using h
  · exact (hL.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
      (show ‖z-x‖ ≤ ‖y-x‖ by simpa only [mem_closedBall,dist_eq_norm] using hz) L.coe_nonneg)

theorem lazy_prediction_remainder {g : E → F} (hg : Differentiable ℝ g)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ g))
    (B : E →L[ℝ] F) (z y snapshot : E) {δ : ℝ}
    (hB : ‖B-fderiv ℝ g snapshot‖ ≤ δ) :
    ‖g z+B (y-z)-g y‖ ≤
      ((L : ℝ)*‖y-z‖+(L : ℝ)*‖snapshot-z‖+δ)*‖y-z‖ := by
  have ht := first_taylor_remainder hg hL z y
  have hd : ‖B-fderiv ℝ g z‖ ≤ δ+(L : ℝ)*‖snapshot-z‖ := by
    calc
      ‖B-fderiv ℝ g z‖ ≤ ‖B-fderiv ℝ g snapshot‖+‖fderiv ℝ g snapshot-fderiv ℝ g z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ+(L : ℝ)*‖snapshot-z‖ := add_le_add hB (hL.norm_sub_le snapshot z)
  have he : g z+B (y-z)-g y =
      -(g y-g z-fderiv ℝ g z (y-z))+(B-fderiv ℝ g z) (y-z) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  calc
    ‖-(g y-g z-fderiv ℝ g z (y-z))+(B-fderiv ℝ g z) (y-z)‖ ≤
        ‖g y-g z-fderiv ℝ g z (y-z)‖+‖(B-fderiv ℝ g z) (y-z)‖ := by
      simpa only [norm_neg] using norm_add_le (-(g y-g z-fderiv ℝ g z (y-z))) ((B-fderiv ℝ g z) (y-z))
    _ ≤ (L : ℝ)*‖y-z‖^2+(δ+(L : ℝ)*‖snapshot-z‖)*‖y-z‖ :=
      add_le_add ht (((B-fderiv ℝ g z).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
    _ = _ := by ring

end GradientHessian.Nalen
