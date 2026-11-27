import Nonsmooth.FiniteComparisonCone
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cone_weighted_displacement {u w e : E} {δ ε a t : ℝ}
    (he : ‖e‖ = 1) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hw : ‖w‖ ≤ a * ε)
    (hslope : δ * ‖u‖ + (1 + δ) * ε * t ≤ ⟪u, e⟫_ℝ) :
    δ * ‖a • u + t • w‖ ≤ ⟪a • u + t • w, e⟫_ℝ := by
  have hnorm : ‖a • u + t • w‖ ≤ a * ‖u‖ + t * ‖w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg ht]
      using norm_add_le (a • u) (t • w)
  have hinner : -‖w‖ ≤ ⟪w, e⟫_ℝ := by
    have h := (abs_le.mp (abs_real_inner_le_norm w e)).1
    simpa only [he, mul_one] using h
  have h1 := mul_le_mul_of_nonneg_left hslope ha
  have h2 := mul_le_mul_of_nonneg_left hw (mul_nonneg (by linarith : 0 ≤ 1 + δ) ht)
  have h3 := mul_le_mul_of_nonneg_left hinner ht
  have h4 := mul_le_mul_of_nonneg_left hnorm hδ
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith

theorem cone_displacement_rescale {v e : E} {δ s : ℝ}
    (hs : 0 ≤ s) (hv : δ * ‖v‖ ≤ ⟪v, e⟫_ℝ) :
    δ * ‖s • v‖ ≤ ⟪s • v, e⟫_ℝ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, real_inner_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left hv hs]

/-- A segment to the query on the opposite side transfers a section cone to a larger space. -/
theorem convex_cone_lift_nonnegative {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) (H : Submodule ℝ E) (x u w n e : E) {B δ ε a t : ℝ}
    (hu : u ∈ H) (hwH : w ∈ H) (he : ‖e‖ = 1) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ht : 0 ≤ t) (hw : ‖w‖ ≤ a * ε)
    (hqG : x + w - a • n ∈ G) (hqB : f (x + w - a • n) ≤ B)
    (hsection : ∀ v ∈ H, x + v ∈ G → δ * ‖v‖ ≤ ⟪v, e⟫_ℝ → B ≤ f (x + v))
    (hzG : x + u + t • n ∈ G)
    (hslope : δ * ‖u‖ + (1 + δ) * ε * t ≤ ⟪u, e⟫_ℝ) :
    B ≤ f (x + u + t • n) := by
  let s : ℝ := 1 / (a + t)
  let v := s • (a • u + t • w)
  have hden : 0 < a + t := by linarith
  have hs : 0 < s := one_div_pos.mpr hden
  have hsum : s * t + s * a = 1 := by dsimp [s]; field_simp; ring
  have hα : 0 ≤ s * t := mul_nonneg hs.le ht
  have hβ : 0 < s * a := mul_pos hs ha
  have heq : (s * t) • (x + w - a • n) + (s * a) • (x + u + t • n) = x + v := by
    calc
      _ = (s * t + s * a) • x + s • (a • u + t • w) := by module
      _ = x + v := by rw [hsum, one_smul]
  have hvH : v ∈ H := H.smul_mem s (H.add_mem (H.smul_mem a hu) (H.smul_mem t hwH))
  have hvG : x + v ∈ G := by
    rw [← heq]
    exact hf.1 hqG hzG hα hβ.le hsum
  have hvcone : δ * ‖v‖ ≤ ⟪v, e⟫_ℝ :=
    cone_displacement_rescale hs.le (cone_weighted_displacement he hδ ha.le ht hw hslope)
  have hBv := hsection v hvH hvG hvcone
  have hc := hf.2 hqG hzG hα hβ.le hsum
  rw [heq] at hc
  simp only [smul_eq_mul] at hc
  have hqmul := mul_le_mul_of_nonneg_left hqB hα
  by_contra hlt
  have hgap := mul_pos hβ (sub_pos.mpr (lt_of_not_ge hlt))
  have hsumB : s * t * B + s * a * B = B := by rw [← add_mul, hsum, one_mul]
  nlinarith only [hBv, hc, hqmul, hgap, hsumB]

end
end Nonsmooth
