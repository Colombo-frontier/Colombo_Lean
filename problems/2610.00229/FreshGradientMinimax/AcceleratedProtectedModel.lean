import FreshGradientMinimax.AcceleratedCapSmooth

/-! The protected intrinsic objective satisfies the original K=10^8
global smoothness certificate, using its actual gradients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem acceleratedProtectedGradientU_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedProtectedGradientU n k δ u y - acceleratedProtectedGradientU n k δ v y‖ ≤ 14196 * ‖u - v‖ := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v)
    (acceleratedCapGradientU n k δ u y - acceleratedCapGradientU n k δ v y)
  have he : acceleratedProtectedGradientU n k δ u y - acceleratedProtectedGradientU n k δ v y =
      (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k δ v) -
        (acceleratedCapGradientU n k δ u y - acceleratedCapGradientU n k δ v y) := by
    unfold acceleratedProtectedGradientU
    abel
  rw [he]
  linarith only [h, acceleratedPrimalGradient_difference hn hδ u v,
    acceleratedCapGradientU_difference_u hn hδ u v y]

theorem acceleratedProtectedGradientU_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedProtectedGradientU n k δ u y - acceleratedProtectedGradientU n k δ u z‖ ≤ 1421 * ‖y - z‖ := by
  simpa only [acceleratedProtectedGradientU, sub_sub_sub_cancel_left, norm_sub_rev] using
    acceleratedCapGradientU_difference_y hn hδ u y z

theorem acceleratedProtectedGradientY_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedProtectedGradientY n k δ u y - acceleratedProtectedGradientY n k δ v y‖ ≤ 1421 * ‖u - v‖ := by
  simpa only [acceleratedProtectedGradientY, sub_sub_sub_cancel_left, norm_sub_rev] using
    acceleratedCapGradientY_difference_u hn hδ u v y

theorem acceleratedProtectedGradientY_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedProtectedGradientY n k δ u y - acceleratedProtectedGradientY n k δ u z‖ ≤ 10041 * ‖y - z‖ := by
  have he : acceleratedProtectedGradientY n k δ u y - acceleratedProtectedGradientY n k δ u z =
      -(robinStep (n + 2) ^ 2 • (y - z)) - (acceleratedCapGradientY n k δ u y - acceleratedCapGradientY n k δ u z) := by
    simp only [acceleratedProtectedGradientY, smul_sub]
    abel
  rw [he]
  have h := norm_sub_le (-(robinStep (n + 2) ^ 2 • (y - z)))
    (acceleratedCapGradientY n k δ u y - acceleratedCapGradientY n k δ u z)
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  have hs := mul_le_mul_of_nonneg_right (robinStep_sq_le_one n) (norm_nonneg (y - z))
  nlinarith only [h, hs, acceleratedCapGradientY_difference_y hn hδ u y z]

def acceleratedProtectedModel (n k : ℕ) (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    NCObjective (k * 2 + 1) (k * (n + 2)) (10 ^ 8) (robinStep (n + 2) ^ 2) where
  μ_pos := sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))
  μ_le_L := (robinStep_sq_le_one n).trans (by norm_num)
  f := acceleratedProtected n k δ
  gradX := acceleratedProtectedGradientU n k δ
  gradY := acceleratedProtectedGradientY n k δ
  derivative := acceleratedProtected_hasFDerivAt_joint n k hδ
  joint_smooth := by
    intro x y z w
    apply joint_smooth_of_four_blocks (by norm_num : (0 : ℝ) ≤ 10 ^ 8) ?_ ?_ ?_ ?_ x z y w
    · intro a b c
      exact (acceleratedProtectedGradientU_difference_u hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedProtectedGradientU_difference_y hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedProtectedGradientY_difference_u hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedProtectedGradientY_difference_y hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  dual_strong := acceleratedProtected_strongConcave n k hδ

theorem acceleratedProtectedModel_gradient_bound {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖(acceleratedProtectedModel n k hn hδ).gradX u y‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ) :=
  (acceleratedProtectedGradientU_norm hn hδ u y).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

theorem acceleratedProtectedModel_origin_dual {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (acceleratedProtectedModel n k hn hδ).dualMax 0 = 0 := by
  apply ((acceleratedProtectedModel n k hn hδ).dualMax_unique 0 0 ?_).symm
  intro y
  change acceleratedProtected n k δ 0 y ≤ acceleratedProtected n k δ 0 0
  rw [acceleratedProtected_origin hn hδ]
  exact acceleratedProtected_origin_max hn hδ y

theorem acceleratedProtectedModel_localized {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (acceleratedProtectedModel n k hn hδ).DualLocalized 0 := by
  change ‖acceleratedProtectedGradientY n k δ 0 0‖ ≤ 0
  rw [acceleratedProtectedGradientY_origin n k hδ, norm_zero]

theorem acceleratedProtectedModel_gap {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) :
    (acceleratedProtectedModel n k hn (acceleratedThreshold_pos n hk).le).PrimalGapAtMost (1000 * (k + 1 : ℕ)) := by
  intro u
  change acceleratedProtectedValue n k (acceleratedThreshold n k) 0 -
    acceleratedProtectedValue n k (acceleratedThreshold n k) u ≤ _
  rw [acceleratedProtectedValue_origin hn (acceleratedThreshold_pos n hk).le]
  linarith only [acceleratedProtectedValue_lower hn hk u, coreTheta_pos 0]

end FreshGradientMinimax
