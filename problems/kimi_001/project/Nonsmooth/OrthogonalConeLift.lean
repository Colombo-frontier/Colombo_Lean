import Nonsmooth.ConeSectionLift

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_cone_lift_two_sided {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) (H : Submodule ℝ E) (x u w n e : E) {B δ ε a t : ℝ}
    (hu : u ∈ H) (hwH : w ∈ H) (he : ‖e‖ = 1) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hw : ‖w‖ ≤ a * ε)
    (hqminusG : x + w - a • n ∈ G) (hqplusG : x + w + a • n ∈ G)
    (hqminusB : f (x + w - a • n) ≤ B) (hqplusB : f (x + w + a • n) ≤ B)
    (hsection : ∀ v ∈ H, x + v ∈ G → δ * ‖v‖ ≤ ⟪v, e⟫_ℝ → B ≤ f (x + v))
    (hzG : x + u + t • n ∈ G)
    (hslope : δ * ‖u‖ + (1 + δ) * ε * |t| ≤ ⟪u, e⟫_ℝ) :
    B ≤ f (x + u + t • n) := by
  by_cases ht : 0 ≤ t
  · exact convex_cone_lift_nonnegative hf H x u w n e hu hwH he hδ ha ht hw
      hqminusG hqminusB hsection hzG (by simpa only [abs_of_nonneg ht] using hslope)
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_lt (lt_of_not_ge ht))
    have hqG : x + w - a • (-n) ∈ G := by simpa only [smul_neg, sub_neg_eq_add] using hqplusG
    have hqB : f (x + w - a • (-n)) ≤ B := by
      simpa only [smul_neg, sub_neg_eq_add] using hqplusB
    have hzG' : x + u + (-t) • (-n) ∈ G := by simpa only [neg_smul_neg] using hzG
    have hslope' : δ * ‖u‖ + (1 + δ) * ε * (-t) ≤ ⟪u, e⟫_ℝ := by
      simpa only [abs_of_neg (lt_of_not_ge ht)] using hslope
    simpa only [neg_smul_neg] using convex_cone_lift_nonnegative hf H x u w (-n) e
      hu hwH he hδ ha ht' hw hqG hqB hsection hzG' hslope'

theorem orthogonal_cone_coefficient_bound {u n : E} (hn : ‖n‖ = 1)
    (hun : ⟪u, n⟫_ℝ = 0) (δ c t : ℝ) :
    δ * ‖u‖ + c * |t| ≤ Real.sqrt (δ ^ 2 + c ^ 2) * ‖u + t • n‖ := by
  have hnorm : ‖u + t • n‖ ^ 2 = ‖u‖ ^ 2 + |t| ^ 2 := by
    rw [norm_add_sq_real]
    simp only [real_inner_smul_right, hun, mul_zero, add_zero, norm_smul,
      Real.norm_eq_abs, hn, mul_one]
  have hs : (δ * ‖u‖ + c * |t|) ^ 2 ≤ (δ ^ 2 + c ^ 2) * (‖u‖ ^ 2 + |t| ^ 2) := by
    nlinarith [sq_nonneg (δ * |t| - c * ‖u‖)]
  have hr : (Real.sqrt (δ ^ 2 + c ^ 2) * ‖u + t • n‖) ^ 2 =
      (δ ^ 2 + c ^ 2) * (‖u‖ ^ 2 + |t| ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hnorm]
  have hpos : 0 ≤ Real.sqrt (δ ^ 2 + c ^ 2) * ‖u + t • n‖ := by positivity
  nlinarith only [hs, hr, hpos]

/-- The angular coefficient grows by a Euclidean square sum when lifting one orthogonal direction. -/
theorem convex_cone_lift_orthogonal {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) (H : Submodule ℝ E) (x u w n e : E) {B δ ε a t : ℝ}
    (hu : u ∈ H) (hwH : w ∈ H) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hun : ⟪u, n⟫_ℝ = 0) (hne : ⟪n, e⟫_ℝ = 0) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hw : ‖w‖ ≤ a * ε)
    (hqminusG : x + w - a • n ∈ G) (hqplusG : x + w + a • n ∈ G)
    (hqminusB : f (x + w - a • n) ≤ B) (hqplusB : f (x + w + a • n) ≤ B)
    (hsection : ∀ v ∈ H, x + v ∈ G → δ * ‖v‖ ≤ ⟪v, e⟫_ℝ → B ≤ f (x + v))
    (hzG : x + u + t • n ∈ G)
    (hslope : Real.sqrt (δ ^ 2 + ((1 + δ) * ε) ^ 2) * ‖u + t • n‖ ≤
      ⟪u + t • n, e⟫_ℝ) :
    B ≤ f (x + u + t • n) := by
  apply convex_cone_lift_two_sided hf H x u w n e hu hwH he hδ ha hw
    hqminusG hqplusG hqminusB hqplusB hsection hzG
  have hb := (orthogonal_cone_coefficient_bound hn hun δ ((1 + δ) * ε) t).trans hslope
  simpa only [inner_add_left, real_inner_smul_left, hne, mul_zero, add_zero] using hb

end
end Nonsmooth
