import FreshGradientMinimax.FramedAcceleratedCapSmooth
import FreshGradientMinimax.FramedAcceleratedValue

/-! The full ambient construction as a genuine NC--SC objective with the
original K=10^8 and inverse-square strong concavity. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
theorem framedAcceleratedGradientU_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedGradientU V δ u y - framedAcceleratedGradientU V δ v y‖ ≤ 14196 * ‖u - v‖ := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v)
    (framedAcceleratedCapGradientU V δ u y - framedAcceleratedCapGradientU V δ v y)
  have he : framedAcceleratedGradientU V δ u y - framedAcceleratedGradientU V δ v y =
      (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v) -
        (framedAcceleratedCapGradientU V δ u y - framedAcceleratedCapGradientU V δ v y) := by
    unfold framedAcceleratedGradientU
    abel
  rw [he]
  linarith only [h, acceleratedPrimalGradient_difference hn hδ u v,
    framedAcceleratedCapGradientU_difference_u V hn hδ u v y]

theorem framedAcceleratedGradientU_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedAcceleratedGradientU V δ u y - framedAcceleratedGradientU V δ u z‖ ≤ 1421 * ‖y - z‖ := by
  simpa only [framedAcceleratedGradientU, sub_sub_sub_cancel_left, norm_sub_rev] using
    framedAcceleratedCapGradientU_difference_y V hn hδ u y z

theorem framedAcceleratedGradientY_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedGradientY V δ u y - framedAcceleratedGradientY V δ v y‖ ≤ 1421 * ‖u - v‖ := by
  simpa only [framedAcceleratedGradientY, sub_sub_sub_cancel_left, norm_sub_rev] using
    framedAcceleratedCapGradientY_difference_u V hn hδ u v y

theorem framedAcceleratedGradientY_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedAcceleratedGradientY V δ u y - framedAcceleratedGradientY V δ u z‖ ≤ 10041 * ‖y - z‖ := by
  have he : framedAcceleratedGradientY V δ u y - framedAcceleratedGradientY V δ u z =
      -(robinStep (n + 2) ^ 2 • (y - z)) - (framedAcceleratedCapGradientY V δ u y - framedAcceleratedCapGradientY V δ u z) := by
    simp only [framedAcceleratedGradientY, smul_sub]
    abel
  rw [he]
  have h := norm_sub_le (-(robinStep (n + 2) ^ 2 • (y - z)))
    (framedAcceleratedCapGradientY V δ u y - framedAcceleratedCapGradientY V δ u z)
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  have hs := mul_le_mul_of_nonneg_right (robinStep_sq_le_one n) (norm_nonneg (y - z))
  nlinarith only [h, hs, framedAcceleratedCapGradientY_difference_y V hn hδ u y z]

def framedAcceleratedModel (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    NCObjective (k * 2 + 1) dy (10 ^ 8) (robinStep (n + 2) ^ 2) where
  μ_pos := sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))
  μ_le_L := (robinStep_sq_le_one n).trans (by norm_num)
  f := framedAcceleratedProtected V δ
  gradX := framedAcceleratedGradientU V δ
  gradY := framedAcceleratedGradientY V δ
  derivative := framedAcceleratedProtected_hasFDerivAt_joint V hδ
  joint_smooth := by
    intro x y z w
    apply joint_smooth_of_four_blocks (by norm_num : (0 : ℝ) ≤ 10 ^ 8) ?_ ?_ ?_ ?_ x z y w
    · intro a b c
      exact (framedAcceleratedGradientU_difference_u V hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (framedAcceleratedGradientU_difference_y V hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (framedAcceleratedGradientY_difference_u V hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (framedAcceleratedGradientY_difference_y V hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  dual_strong := framedAcceleratedProtected_strongConcave V hδ

theorem framedAcceleratedModel_gradient_bound (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖(framedAcceleratedModel V hn hδ).gradX u y‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ) :=
  (framedAcceleratedGradientU_norm V hn hδ u y).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

theorem framedAcceleratedModel_origin_dual (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (framedAcceleratedModel V hn hδ).dualMax 0 = 0 := by
  apply ((framedAcceleratedModel V hn hδ).dualMax_unique 0 0 ?_).symm
  intro y
  change framedAcceleratedProtected V δ 0 y ≤ framedAcceleratedProtected V δ 0 0
  rw [framedAcceleratedProtected_origin V hn hδ]
  exact framedAcceleratedProtected_origin_max V hn hδ y

theorem framedAcceleratedModel_localized (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (framedAcceleratedModel V hn hδ).DualLocalized 0 := by
  change ‖framedAcceleratedGradientY V δ 0 0‖ ≤ 0
  rw [framedAcceleratedGradientY_origin V hδ, norm_zero]

theorem framedAcceleratedModel_gap (hn : 10 ≤ n + 2) (hk : 0 < k) :
    (framedAcceleratedModel V hn (acceleratedThreshold_pos n hk).le).PrimalGapAtMost (1000 * (k + 1 : ℕ)) := by
  intro u
  change framedAcceleratedValue V (acceleratedThreshold n k) 0 -
    framedAcceleratedValue V (acceleratedThreshold n k) u ≤ _
  rw [framedAcceleratedValue_origin V hn (acceleratedThreshold_pos n hk).le]
  linarith only [framedAcceleratedValue_lower V hn hk u, coreTheta_pos 0]

end FreshGradientMinimax
