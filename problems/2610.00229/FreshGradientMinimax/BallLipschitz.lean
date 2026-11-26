import FreshGradientMinimax.QuadraticConvexity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.Convex

/-! A Lipschitz bound on a closed ball extends without loss when the function
is constant on its boundary and exterior. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

theorem exists_boundary_between {R : ℝ} {x y : E} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
    ∃ z : E, ‖z‖ = R ∧ ‖x - z‖ ≤ ‖x - y‖ := by
  have hc : ContinuousOn (fun s : ℝ => ‖x + s • (y - x)‖) (Set.Icc 0 1) := by fun_prop
  have hr : R ∈ Set.Icc (‖x + (0 : ℝ) • (y - x)‖) (‖x + (1 : ℝ) • (y - x)‖) := by
    simpa only [zero_smul, add_zero, one_smul, add_sub_cancel] using And.intro hx hy
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc hr
  refine ⟨x + s • (y - x), hz, ?_⟩
  rw [norm_sub_rev x, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1,
    norm_sub_rev y]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

theorem ball_bound_constant_outside {f : E → F} {C R : ℝ} (hC : 0 ≤ C) (c : F)
    (hin : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ C * ‖x - y‖)
    (hout : ∀ x, R ≤ ‖x‖ → f x = c) (x y : E) : ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  have cross (a b : E) (ha : ‖a‖ ≤ R) (hb : R ≤ ‖b‖) :
      ‖f a - f b‖ ≤ C * ‖a - b‖ := by
    obtain ⟨z, hz, hd⟩ := exists_boundary_between ha hb
    rw [hout b hb, ← hout z hz.ge]
    exact (hin a z ha hz.le).trans (mul_le_mul_of_nonneg_left hd hC)
  by_cases hx : ‖x‖ ≤ R
  · by_cases hy : ‖y‖ ≤ R
    · exact hin x y hx hy
    · exact cross x y hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ R
    · simpa only [norm_sub_rev] using cross y x hy (le_of_not_ge hx)
    · rw [hout x (le_of_not_ge hx), hout y (le_of_not_ge hy), sub_self, norm_zero]
      positivity

end Normed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_gradient_bound_on_ball {f : E → ℝ} {G : E → E} {C R : ℝ}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x, ‖x‖ ≤ R → ‖G x‖ ≤ C) {x y : E} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |f x - f y| ≤ C * ‖x - y‖ := by
  have h := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt)
    (fun z hz => by
      rw [innerSL_apply_norm]
      exact hG z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  simpa only [Real.norm_eq_abs] using h

theorem scalar_gradient_bound_global {f : E → ℝ} {G : E → E} {C : ℝ}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (hG : ∀ x, ‖G x‖ ≤ C) (x y : E) :
    |f x - f y| ≤ C * ‖x - y‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt)
    (fun z _ => by rw [innerSL_apply_norm]; exact hG z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

end FreshGradientMinimax
