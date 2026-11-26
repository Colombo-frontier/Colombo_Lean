import FreshGradientMinimax.BallLipschitz

/-! Algebraic estimates for a convex blend of vector fields. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_vector_difference (b c : ℝ) (x y : E) (hc : 0 ≤ c ∧ c ≤ 1) :
    ‖(1 - b) • x - (1 - c) • y‖ ≤ ‖x - y‖ + |b - c| * ‖x‖ := by
  have he : (1 - b) • x - (1 - c) • y = (1 - c) • (x - y) + (c - b) • x := by module
  rw [he]
  have h := norm_add_le ((1 - c) • (x - y)) ((c - b) • x)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hc.2), abs_sub_comm c] at h
  have hh := mul_le_of_le_one_left (norm_nonneg (x - y)) (show 1 - c ≤ 1 by linarith [hc.1])
  linarith only [h, hh]

theorem convex_blend_difference (b c : ℝ) (x x' y y' : E) (hc : 0 ≤ c ∧ c ≤ 1)
    {D : ℝ} (hx : ‖x - x'‖ ≤ D) (hy : ‖y - y'‖ ≤ D) :
    ‖((1 - b) • x + b • y) - ((1 - c) • x' + c • y')‖ ≤ D + |b - c| * ‖y - x‖ := by
  have he : ((1 - b) • x + b • y) - ((1 - c) • x' + c • y') =
      ((1 - c) • (x - x') + c • (y - y')) + (b - c) • (y - x) := by module
  have h := norm_add_le ((1 - c) • (x - x')) (c • (y - y'))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hc.2), abs_of_nonneg hc.1] at h
  have h1 := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hc.2)
  have h2 := mul_le_mul_of_nonneg_left hy hc.1
  have hb : ‖(1 - c) • (x - x') + c • (y - y')‖ ≤ D := by nlinarith only [h, h1, h2]
  rw [he]
  calc
    _ ≤ ‖(1 - c) • (x - x') + c • (y - y')‖ + ‖(b - c) • (y - x)‖ := norm_add_le _ _
    _ ≤ _ := by simpa only [norm_smul, Real.norm_eq_abs] using add_le_add_right hb ‖(b - c) • (y - x)‖

theorem nonnegative_smul_difference {a : ℝ} (ha : 0 ≤ a) (x y : E) :
    ‖a • x - a • y‖ = a * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]

theorem weighted_vector_difference_bound (b c : ℝ) (x y : E) (hc : 0 ≤ c ∧ c ≤ 1)
    {A B C L δ : ℝ} (hδ : 0 ≤ δ) (hx : ‖x‖ ≤ A) (hxy : ‖x - y‖ ≤ L * δ)
    (hbc : |b - c| ≤ B * δ) (hBA : B * A ≤ C) :
    ‖(1 - b) • x - (1 - c) • y‖ ≤ (L + C) * δ := by
  have h := weighted_vector_difference b c x y hc
  have hp := mul_le_mul hbc hx (norm_nonneg x) ((abs_nonneg _).trans hbc)
  have hh := mul_le_mul_of_nonneg_right hBA hδ
  nlinarith only [h, hp, hh, hxy]

theorem convex_blend_difference_bound (b c : ℝ) (x x' y y' : E) (hc : 0 ≤ c ∧ c ≤ 1)
    {A B C L δ : ℝ} (hδ : 0 ≤ δ) (hx : ‖x - x'‖ ≤ L * δ) (hy : ‖y - y'‖ ≤ L * δ)
    (hgap : ‖y - x‖ ≤ A) (hbc : |b - c| ≤ B * δ) (hBA : B * A ≤ C) :
    ‖((1 - b) • x + b • y) - ((1 - c) • x' + c • y')‖ ≤ (L + C) * δ := by
  have h := convex_blend_difference b c x x' y y' hc hx hy
  have hp := mul_le_mul hbc hgap (norm_nonneg _) ((abs_nonneg _).trans hbc)
  have hh := mul_le_mul_of_nonneg_right hBA hδ
  nlinarith only [h, hp, hh]

end FreshGradientMinimax
