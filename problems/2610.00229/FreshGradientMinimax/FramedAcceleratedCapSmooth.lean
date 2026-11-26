import FreshGradientMinimax.FramedAcceleratedCapControl
import FreshGradientMinimax.BlendDifference

/-! Global ambient cap gradient bounds, including both joining interfaces. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
theorem framedAcceleratedCapGradientU_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedCapGradientU V δ u y - framedAcceleratedCapGradientU V δ v y‖ ≤ 10196 * ‖u - v‖ := by
  have h := weighted_vector_difference_bound _ _ _ _ (framedAcceleratedCapWeight_bounds V δ v y)
    (norm_nonneg (u - v)) (framedRobinGradientU_norm_radius V hn hδ u y)
    (framedRobinGradientU_difference_u V hn hδ u v y) (framedAcceleratedCapWeight_difference_u V hn hδ u v y)
    (show (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (14 * acceleratedDualRadius n k) ≤ 196 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem framedAcceleratedCapGradientU_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedAcceleratedCapGradientU V δ u y - framedAcceleratedCapGradientU V δ u z‖ ≤ 1421 * ‖y - z‖ := by
  have h := weighted_vector_difference_bound _ _ _ _ (framedAcceleratedCapWeight_bounds V δ u z)
    (norm_nonneg (y - z)) (framedRobinGradientU_norm_radius V hn hδ u y)
    (framedRobinGradientU_difference_y V hn hδ u y z) (framedAcceleratedCapWeight_difference_y V hn hδ u y z)
    (show (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (14 * acceleratedDualRadius n k) ≤ 1400 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem framedAcceleratedCapGradientY_gap_form (δ : ℝ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedAcceleratedCapGradientY V δ u y = (40 : ℝ) • y -
      (1 - framedAcceleratedCapWeight V δ u y) • framedAcceleratedGapGradientY V δ u y := by
  unfold framedAcceleratedCapGradientY framedAcceleratedGapGradientY
  module

theorem framedAcceleratedCapGradientY_exterior (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    framedAcceleratedCapGradientY V δ u y = (40 : ℝ) • y := by
  simp only [framedAcceleratedCapGradientY, framedAcceleratedCapWeight_exterior V hn hδ u y hy,
    sub_self, zero_smul, one_smul, zero_add]

theorem framedAcceleratedCapGradientY_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedCapGradientY V δ u y - framedAcceleratedCapGradientY V δ v y‖ ≤ 1421 * ‖u - v‖ := by
  by_cases hy : 2 * acceleratedDualRadius n k ≤ ‖y‖
  · rw [framedAcceleratedCapGradientY_exterior V hn hδ u y hy, framedAcceleratedCapGradientY_exterior V hn hδ v y hy,
      sub_self, norm_zero]
    positivity
  · have hd : ‖framedAcceleratedGapGradientY V δ u y - framedAcceleratedGapGradientY V δ v y‖ ≤ 21 * ‖u - v‖ := by
      simpa only [framedAcceleratedGapGradientY, sub_sub_sub_cancel_left, norm_sub_rev] using
        framedRobinGradientY_difference_u V hn hδ u v y
    have h := weighted_vector_difference_bound _ _ _ _ (framedAcceleratedCapWeight_bounds V δ v y)
      (norm_nonneg (u - v)) (framedAcceleratedGapGradientY_norm_on_ball V hn hδ u y (le_of_not_ge hy)) hd
      (framedAcceleratedCapWeight_difference_u V hn hδ u v y)
      (show (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
          (100 * acceleratedDualRadius n k) ≤ 1400 by
        rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
    norm_num only at h
    simpa only [framedAcceleratedCapGradientY_gap_form, sub_sub_sub_cancel_left, norm_sub_rev] using h

theorem framedAcceleratedCapGradientY_difference_y_from_ball (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) (hy : ‖y‖ ≤ 2 * acceleratedDualRadius n k) :
    ‖framedAcceleratedCapGradientY V δ u y - framedAcceleratedCapGradientY V δ u z‖ ≤ 10040 * ‖y - z‖ := by
  have hq : ‖framedRobinGradientY V δ u y - framedRobinGradientY V δ u z‖ ≤ 40 * ‖y - z‖ :=
    (framedRobinGradientY_difference_y V hδ u y z).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  have hw : ‖(40 : ℝ) • y - (40 : ℝ) • z‖ ≤ 40 * ‖y - z‖ :=
    (nonnegative_smul_difference (by norm_num : (0 : ℝ) ≤ 40) y z).le
  have h := convex_blend_difference_bound _ _ _ _ _ _ (framedAcceleratedCapWeight_bounds V δ u z)
    (norm_nonneg (y - z)) hq hw (framedAcceleratedGapGradientY_norm_on_ball V hn hδ u y hy)
    (framedAcceleratedCapWeight_difference_y V hn hδ u y z)
    (show (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (100 * acceleratedDualRadius n k) ≤ 10000 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem framedAcceleratedCapGradientY_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    ‖framedAcceleratedCapGradientY V δ u y - framedAcceleratedCapGradientY V δ u z‖ ≤ 10040 * ‖y - z‖ := by
  by_cases hy : 2 * acceleratedDualRadius n k ≤ ‖y‖
  · by_cases hz : 2 * acceleratedDualRadius n k ≤ ‖z‖
    · rw [framedAcceleratedCapGradientY_exterior V hn hδ u y hy, framedAcceleratedCapGradientY_exterior V hn hδ u z hz,
        nonnegative_smul_difference (by norm_num : (0 : ℝ) ≤ 40)]
      exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
    · simpa only [norm_sub_rev] using framedAcceleratedCapGradientY_difference_y_from_ball V hn hδ u z y (le_of_not_ge hz)
  · exact framedAcceleratedCapGradientY_difference_y_from_ball V hn hδ u y z (le_of_not_ge hy)

end FreshGradientMinimax
