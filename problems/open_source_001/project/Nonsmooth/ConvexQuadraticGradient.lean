import Nonsmooth.StrongPotentialVariance
import Mathlib.Analysis.Calculus.Deriv.Comp

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_potential_affine_line (U : E → ℝ) (hc : ConvexOn ℝ univ U) (x u : E) :
    ConvexOn ℝ univ (fun t : ℝ => U (x + t • u)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ c d hc0 hd0 hcd
  have he : x + (c * a + d * b) • u = c • (x + a • u) + d • (x + b • u) := by
    calc
      _ = (c + d) • x + (c * a + d * b) • u := by rw [hcd, one_smul]
      _ = _ := by simp only [add_smul, smul_add, smul_smul]; abel
  simpa only [smul_eq_mul, he] using hc.2 (mem_univ (x + a • u))
    (mem_univ (x + b • u)) hc0 hd0 hcd

/-- Convexity and a quadratic bound give linear growth of the derivative.
The step length grows with the base point, so the estimate remains linear. -/
theorem convex_quadratic_directional_upper (U : E → ℝ) (hc : ConvexOn ℝ univ U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |U y| ≤ C * (1 + ‖y‖ ^ 2))
    (x : E) (L : E →L[ℝ] ℝ) (hd : HasFDerivAt U L x) (u : E) (hu : ‖u‖ ≤ 1) :
    L u ≤ 6 * C * (1 + ‖x‖) := by
  let r := 1 + ‖x‖
  have hr : 0 < r := by dsimp only [r]; positivity
  have hline : HasDerivAt (fun t : ℝ => U (x + t • u)) (L u) 0 := by
    have hg : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
    exact hd.comp_hasDerivAt_of_eq 0 hg (by simp)
  have hs := (convex_potential_affine_line U hc x u).le_slope_of_hasDerivAt
    (mem_univ 0) (mem_univ r) hr hline
  simp only [slope_def_field, zero_smul, add_zero, sub_zero] at hs
  have hs' := (le_div_iff₀ hr).mp hs
  have hn : ‖x + r • u‖ ≤ 1 + 2 * ‖x‖ := by
    calc
      _ ≤ ‖x‖ + ‖r • u‖ := norm_add_le _ _
      _ = ‖x‖ + r * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ ‖x‖ + r * 1 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hu hr.le)
      _ = _ := by dsimp only [r]; ring
  have hsq := (sq_le_sq₀ (norm_nonneg (x + r • u)) (by positivity : 0 ≤ 1 + 2 * ‖x‖)).mpr hn
  have hdif : U (x + r • u) - U x ≤ C * (2 + (1 + 2 * ‖x‖) ^ 2 + ‖x‖ ^ 2) := by
    have h1 := (le_abs_self (U (x + r • u))).trans (hb (x + r • u))
    have h0 := (neg_abs_le (U x)).trans' (neg_le_neg (hb x))
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  have hpoly : C * (2 + (1 + 2 * ‖x‖) ^ 2 + ‖x‖ ^ 2) ≤ 6 * C * r ^ 2 := by
    have hp : 2 + (1 + 2 * ‖x‖) ^ 2 + ‖x‖ ^ 2 ≤ 6 * (1 + ‖x‖) ^ 2 := by
      nlinarith [norm_nonneg x, sq_nonneg ‖x‖]
    simpa only [r, mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hp hC
  apply (mul_le_mul_iff_of_pos_right hr).mp
  dsimp only [r] at hs' hdif hpoly ⊢
  nlinarith

theorem convex_quadratic_gradient_bound (U : E → ℝ) (hc : ConvexOn ℝ univ U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |U y| ≤ C * (1 + ‖y‖ ^ 2))
    (x : E) (L : E →L[ℝ] ℝ) (hd : HasFDerivAt U L x) :
    ‖L‖ ≤ 6 * C * (1 + ‖x‖) := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := convex_quadratic_directional_upper U hc hC hb x L hd (-u) (by simpa using hu.le)
    rw [map_neg] at h
    linarith
  · exact convex_quadratic_directional_upper U hc hC hb x L hd u hu.le

end
end Nonsmooth
