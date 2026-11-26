import FreshGradientMinimax.AcceleratedPrimalGradient
import FreshGradientMinimax.AcceleratedUncapped
import FreshGradientMinimax.RobinMultiSmooth
import FreshGradientMinimax.JointGradient

/-! Actual partial gradients and all four smoothness blocks of the
uncapped objective. These also justify Danskin's formula independently of
the later radial protection estimates. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedUncappedGradientU (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * 2 + 1) :=
  acceleratedPrimalGradient n k δ u - robinMultiGradientU n k δ u y

theorem acceleratedUncapped_hasFDerivAt_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (fun v => acceleratedUncapped n k δ v y) (innerSL ℝ (acceleratedUncappedGradientU n k δ u y)) u := by
  have h := ((acceleratedPrimal_hasFDerivAt n k hδ u).sub
    (hasFDerivAt_const (robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2) u)).sub
    (robinMultiEnergy_hasFDerivAt_u n k hδ u y)
  apply h.congr_fderiv
  ext v
  simp [acceleratedUncappedGradientU, innerSL_apply, inner_sub_left]

theorem acceleratedUncapped_gradient_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (fun v => acceleratedUncapped n k δ v y) u = acceleratedUncappedGradientU n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedUncapped_hasFDerivAt_u n k hδ u y)).gradient

theorem acceleratedUncapped_gradient_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (acceleratedUncapped n k δ u) y = acceleratedDualGradient n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedUncapped_hasFDerivAt_y n k hδ u y)).gradient

theorem acceleratedUncapped_hasFDerivAt_joint (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (z : Joint (k * 2 + 1) (k * (n + 2))) :
    HasFDerivAt (fun w : Joint (k * 2 + 1) (k * (n + 2)) => acceleratedUncapped n k δ w.1 w.2)
      ((innerSL ℝ (acceleratedUncappedGradientU n k δ z.1 z.2)).coprod
        (innerSL ℝ (acceleratedDualGradient n k δ z.1 z.2))) z := by
  have h := joint_hasFDerivAt_gradient
    ((acceleratedUncapped_joint_contDiff n k hδ).differentiable (by norm_num) z)
  simpa only [acceleratedUncapped_gradient_u n k hδ, acceleratedUncapped_gradient_y n k hδ] using h

theorem acceleratedUncappedGradientU_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedUncappedGradientU n k δ u y‖ ≤ 15000 * Real.sqrt (k + 1 : ℕ) := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u) (robinMultiGradientU n k δ u y)
  change ‖acceleratedUncappedGradientU n k δ u y‖ ≤ _ at h
  linarith only [h, acceleratedPrimalGradient_norm hn hδ u, robinMultiGradientU_norm hn hδ u y]

theorem acceleratedUncappedGradientU_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedUncappedGradientU n k δ u y - acceleratedUncappedGradientU n k δ v y‖ ≤ 14000 * ‖u - v‖ := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v)
    (robinMultiGradientU n k δ u y - robinMultiGradientU n k δ v y)
  have he : acceleratedUncappedGradientU n k δ u y - acceleratedUncappedGradientU n k δ v y =
      (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v) -
        (robinMultiGradientU n k δ u y - robinMultiGradientU n k δ v y) := by
    unfold acceleratedUncappedGradientU
    abel
  rw [he]
  nlinarith only [h, acceleratedPrimalGradient_difference hn hδ u v, robinMultiGradientU_difference_u hn hδ u v y]

theorem acceleratedUncappedGradientU_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedUncappedGradientU n k δ u y - acceleratedUncappedGradientU n k δ u z‖ ≤ 21 * ‖y - z‖ := by
  simpa only [acceleratedUncappedGradientU, sub_sub_sub_cancel_left, norm_sub_rev] using
    robinMultiGradientU_difference_y hn hδ u y z

theorem acceleratedDualGradient_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedDualGradient n k δ u y - acceleratedDualGradient n k δ v y‖ ≤ 21 * ‖u - v‖ := by
  simpa only [acceleratedDualGradient, sub_sub_sub_cancel_left, norm_sub_rev] using
    robinMultiGradientY_difference_u hn hδ u v y

theorem robinStep_sq_le_one (n : ℕ) : robinStep (n + 2) ^ 2 ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
  have hp := (robinStep_pos (show 0 < n + 2 by omega)).le
  change 0 ≤ ((n + 2 : ℕ) : ℝ)⁻¹ at hp
  simp only [one_div, inv_one] at h
  change ((n + 2 : ℕ) : ℝ)⁻¹ ^ 2 ≤ 1
  nlinarith only [h, hp]

theorem acceleratedDualGradient_difference_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedDualGradient n k δ u y - acceleratedDualGradient n k δ u z‖ ≤ 6 * ‖y - z‖ := by
  have he : acceleratedDualGradient n k δ u y - acceleratedDualGradient n k δ u z =
      -(robinStep (n + 2) ^ 2 • (y - z)) - (robinMultiGradientY n k δ u y - robinMultiGradientY n k δ u z) := by
    simp only [acceleratedDualGradient, smul_sub]
    abel
  rw [he]
  have h := norm_sub_le (-(robinStep (n + 2) ^ 2 • (y - z)))
    (robinMultiGradientY n k δ u y - robinMultiGradientY n k δ u z)
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  have hs := mul_le_mul_of_nonneg_right (robinStep_sq_le_one n) (norm_nonneg (y - z))
  nlinarith only [h, hs, robinMultiGradientY_difference_y n k hδ u y z]

end FreshGradientMinimax
