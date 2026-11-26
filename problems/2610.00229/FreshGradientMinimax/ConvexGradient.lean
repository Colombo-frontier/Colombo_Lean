import FreshGradientMinimax.Calculus
import FreshGradientMinimax.DualGeometry

/-! The supporting hyperplane of a genuinely convex differentiable function,
and its conversion into the strong concavity required by NCObjective. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_gradient_support {Q : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ Set.univ Q)
    (hd : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x) (y z : E) :
    Q y + ⟪G y, z - y⟫_ℝ ≤ Q z := by
  let f : ℝ → ℝ := fun t => Q (y + t • (z - y))
  have hf : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht a b ha hb hab
    have h := hc.2 (Set.mem_univ (y + s • (z - y)))
      (Set.mem_univ (y + t • (z - y))) ha hb hab
    have he : y + (a * s + b * t) • (z - y) =
        a • (y + s • (z - y)) + b • (y + t • (z - y)) := by
      have hb' : b = 1 - a := by linarith
      rw [hb']; module
    simpa only [f, smul_eq_mul, he] using h
  have hder : HasDerivAt f ⟪G y, z - y⟫_ℝ 0 := by
    simpa only [zero_smul, add_zero] using along_line_hasDerivAt hd y (z - y) 0
  have h := hf.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hder
  simp only [slope, f, zero_smul, add_zero, one_smul, add_sub_cancel,
    sub_zero, vsub_eq_sub, one_div, one_smul, smul_eq_mul, inv_one, one_mul] at h
  linarith

theorem convex_penalty_strongConcave {Q : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ Set.univ Q)
    (hd : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x) (μ c : ℝ) (v : E) :
    StrongConcaveGradient (fun y => c + ⟪v, y⟫_ℝ - μ / 2 * ‖y‖ ^ 2 - Q y)
      (fun y => v - μ • y - G y) μ := by
  intro y z
  have h := convex_gradient_support hc hd y z
  have hn := norm_sub_sq_real z y
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at *
  rw [hn, show ⟪z, y⟫_ℝ = ⟪y, z⟫_ℝ from real_inner_comm _ _]
  nlinarith only [h]

end FreshGradientMinimax
