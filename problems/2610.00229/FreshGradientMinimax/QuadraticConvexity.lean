import FreshGradientMinimax.ConvexGradient
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Convexity from actual first-order support, including quadratic domination
of a function with a Lipschitz gradient. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_of_gradient_support {f : E → ℝ} {G : E → E}
    (hs : ∀ x y, f x + ⟪G x, y - x⟫_ℝ ≤ f y) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have h1 := mul_le_mul_of_nonneg_left (hs z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hs z y) hb
  have hz : a • (x - z) + b • (y - z) = 0 := by
    dsimp [z]
    have he : b = 1 - a := by linarith
    rw [he]
    module
  have hi := congrArg (fun v => ⟪G z, v⟫_ℝ) hz
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  change f z ≤ a * f x + b * f y
  have hfz : (a + b) * f z = f z := by rw [hab, one_mul]
  nlinarith only [h1, h2, hi, hfz]

theorem half_quadratic_hasFDerivAt (μ : ℝ) (y : E) :
    HasFDerivAt (fun z : E => μ / 2 * ‖z‖ ^ 2) (innerSL ℝ (μ • y)) y := by
  apply ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (μ / 2)).congr_fderiv
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, real_inner_smul_left, smul_eq_mul]
  ring

theorem quadratic_minus_smooth_support {f : E → ℝ} {G : E → E} {L μ : ℝ}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hL : L ≤ μ) (x y : E) :
    (μ / 2 * ‖x‖ ^ 2 - f x) + ⟪μ • x - G x, y - x⟫_ℝ ≤ μ / 2 * ‖y‖ ^ 2 - f y := by
  have hr := (abs_le.mp (smooth_taylor_remainder hd hLip x (y - x))).2
  rw [add_sub_cancel] at hr
  have hn := norm_add_sq_real x (y - x)
  rw [add_sub_cancel] at hn
  have hnμ := congrArg (fun q : ℝ => μ * q) hn
  dsimp only at hnμ
  have hδ := mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg ‖y - x‖)
  simp only [inner_sub_left, real_inner_smul_left]
  nlinarith only [hr, hnμ, hδ]

theorem quadratic_minus_smooth_convex {f : E → ℝ} {G : E → E} {L μ : ℝ}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hL : L ≤ μ) :
    ConvexOn ℝ Set.univ (fun x => μ / 2 * ‖x‖ ^ 2 - f x) :=
  convex_of_gradient_support (quadratic_minus_smooth_support hd hLip hL)

theorem half_quadratic_convex {μ : ℝ} (hμ : 0 ≤ μ) :
    ConvexOn ℝ Set.univ (fun x : E => μ / 2 * ‖x‖ ^ 2) := by
  have h := quadratic_minus_smooth_convex (f := fun _ : E => (0 : ℝ))
    (G := fun _ : E => 0) (L := 0) (μ := μ)
    (fun x => by simpa only [map_zero] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)
    (fun x y => by simp) hμ
  simpa only [sub_zero] using h

end FreshGradientMinimax
