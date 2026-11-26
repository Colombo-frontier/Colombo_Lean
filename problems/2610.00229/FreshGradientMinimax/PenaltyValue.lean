import FreshGradientMinimax.PenaltyObjective

/-! The actual maximized value of the quadratic/convex-penalty family has a
global supporting quadratic. No optimizer differentiability is assumed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {dy : ℕ} (Q : Euclid dy → ℝ) (G : Euclid dy → Euclid dy)
  (L μ d M : ℝ) (u v : Euclid dy) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hu : ‖u‖ ≤ 1)
  (hc : ConvexOn ℝ Set.univ Q) (hd : ∀ y, HasFDerivAt Q (innerSL ℝ (G y)) y)
  (hG : ∀ y y', ‖G y - G y'‖ ≤ L / 8 * ‖y - y'‖)

local notation "F" => penaltyObjective Q G L μ d M u v hμ hκ hu hc hd hG

theorem penaltyObjective_value_support (x z : Euclid 1) :
    (F).value x + ⟪(F).primalGradient x, z - x⟫_ℝ + L / 8 * ‖z - x‖ ^ 2 ≤ (F).value z := by
  have he : (F).value x + ⟪(F).primalGradient x, z - x⟫_ℝ + L / 8 * ‖z - x‖ ^ 2 =
      (F).f z ((F).dualMax x) := by
    rw [(F).value_eq_max x]
    simp only [NCObjective.primalGradient, penaltyObjective, penaltySaddleFunction,
      penaltySaddleGradX, realVector_inner, realCoord_sub]
    rw [← realCoord_norm (z - x), sq_abs, realCoord_sub]
    ring
  rw [he]
  exact (F).le_value z ((F).dualMax x)

theorem penaltyObjective_value_strongMonotone (x z : Euclid 1) :
    L / 4 * ‖z - x‖ ^ 2 ≤ ⟪(F).primalGradient z - (F).primalGradient x, z - x⟫_ℝ := by
  have hx := penaltyObjective_value_support Q G L μ d M u v hμ hκ hu hc hd hG x z
  have hz := penaltyObjective_value_support Q G L μ d M u v hμ hκ hu hc hd hG z x
  rw [norm_sub_rev x z] at hz
  simp only [inner_sub_left, inner_sub_right] at hx hz ⊢
  linarith only [hx, hz]

theorem penaltyObjective_value_gap :
    (F).PrimalGapAtMost (2 * ‖(F).primalGradient 0‖ ^ 2 / L) := by
  have hL : 0 < L := by linarith
  intro z
  have hs := penaltyObjective_value_support Q G L μ d M u v hμ hκ hu hc hd hG 0 z
  simp only [sub_zero] at hs
  have hi := neg_le_abs ⟪(F).primalGradient 0, z⟫_ℝ
  have habs := abs_real_inner_le_norm ((F).primalGradient 0) z
  have hsq := sq_nonneg (‖(F).primalGradient 0‖ - L / 4 * ‖z‖)
  have hm : L * ((F).value 0 - (F).value z) ≤ 2 * ‖(F).primalGradient 0‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (show (F).value 0 - (F).value z ≤
      ‖(F).primalGradient 0‖ * ‖z‖ - L / 8 * ‖z‖ ^ 2 by linarith only [hs, hi, habs]) hL.le
    nlinarith only [h, hsq]
  exact (le_div_iff₀ hL).mpr (by nlinarith only [hm])

end FreshGradientMinimax

