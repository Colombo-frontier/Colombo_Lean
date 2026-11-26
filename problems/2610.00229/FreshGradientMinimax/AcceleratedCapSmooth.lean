import FreshGradientMinimax.AcceleratedCapControl
import FreshGradientMinimax.BlendDifference

/-! All four global gradient blocks of the original accelerated cap.
No second derivative is assumed at the smooth maximum's interfaces. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem acceleratedCapGradientU_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedCapGradientU n k δ u y - acceleratedCapGradientU n k δ v y‖ ≤ 10196 * ‖u - v‖ := by
  have h := weighted_vector_difference_bound _ _ _ _ (acceleratedCapWeight_bounds n k δ v y)
    (norm_nonneg (u - v)) (robinMultiGradientU_norm_radius hn hδ u y)
    (robinMultiGradientU_difference_u hn hδ u v y) (acceleratedCapWeight_difference_u hn hδ u v y)
    (show (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (14 * acceleratedDualRadius n k) ≤ 196 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem acceleratedCapGradientU_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedCapGradientU n k δ u y - acceleratedCapGradientU n k δ u z‖ ≤ 1421 * ‖y - z‖ := by
  have h := weighted_vector_difference_bound _ _ _ _ (acceleratedCapWeight_bounds n k δ u z)
    (norm_nonneg (y - z)) (robinMultiGradientU_norm_radius hn hδ u y)
    (robinMultiGradientU_difference_y hn hδ u y z) (acceleratedCapWeight_difference_y hn hδ u y z)
    (show (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (14 * acceleratedDualRadius n k) ≤ 1400 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem acceleratedCapGradientY_gap_form (n k : ℕ) (δ : ℝ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedCapGradientY n k δ u y = (40 : ℝ) • y -
      (1 - acceleratedCapWeight n k δ u y) • acceleratedGapGradientY n k δ u y := by
  unfold acceleratedCapGradientY acceleratedGapGradientY
  module

theorem acceleratedCapGradientY_exterior {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    acceleratedCapGradientY n k δ u y = (40 : ℝ) • y := by
  simp only [acceleratedCapGradientY, acceleratedCapWeight_exterior hn hδ u y hy,
    sub_self, zero_smul, one_smul, zero_add]

theorem acceleratedCapGradientY_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedCapGradientY n k δ u y - acceleratedCapGradientY n k δ v y‖ ≤ 1421 * ‖u - v‖ := by
  by_cases hy : 2 * acceleratedDualRadius n k ≤ ‖y‖
  · rw [acceleratedCapGradientY_exterior hn hδ u y hy, acceleratedCapGradientY_exterior hn hδ v y hy,
      sub_self, norm_zero]
    positivity
  · have hd : ‖acceleratedGapGradientY n k δ u y - acceleratedGapGradientY n k δ v y‖ ≤ 21 * ‖u - v‖ := by
      simpa only [acceleratedGapGradientY, sub_sub_sub_cancel_left, norm_sub_rev] using
        robinMultiGradientY_difference_u hn hδ u v y
    have h := weighted_vector_difference_bound _ _ _ _ (acceleratedCapWeight_bounds n k δ v y)
      (norm_nonneg (u - v)) (acceleratedGapGradientY_norm_on_ball hn hδ u y (le_of_not_ge hy)) hd
      (acceleratedCapWeight_difference_u hn hδ u v y)
      (show (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
          (100 * acceleratedDualRadius n k) ≤ 1400 by
        rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
    norm_num only at h
    simpa only [acceleratedCapGradientY_gap_form, sub_sub_sub_cancel_left, norm_sub_rev] using h

theorem acceleratedCapGradientY_difference_y_from_ball {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) (hy : ‖y‖ ≤ 2 * acceleratedDualRadius n k) :
    ‖acceleratedCapGradientY n k δ u y - acceleratedCapGradientY n k δ u z‖ ≤ 10040 * ‖y - z‖ := by
  have hq : ‖robinMultiGradientY n k δ u y - robinMultiGradientY n k δ u z‖ ≤ 40 * ‖y - z‖ :=
    (robinMultiGradientY_difference_y n k hδ u y z).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  have hw : ‖(40 : ℝ) • y - (40 : ℝ) • z‖ ≤ 40 * ‖y - z‖ :=
    (nonnegative_smul_difference (by norm_num : (0 : ℝ) ≤ 40) y z).le
  have h := convex_blend_difference_bound _ _ _ _ _ _ (acceleratedCapWeight_bounds n k δ u z)
    (norm_nonneg (y - z)) hq hw (acceleratedGapGradientY_norm_on_ball hn hδ u y hy)
    (acceleratedCapWeight_difference_y hn hδ u y z)
    (show (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) *
        (100 * acceleratedDualRadius n k) ≤ 10000 by
      rw [radius_correction_identity (acceleratedDualRadius_pos n k)]; norm_num)
  norm_num only at h
  exact h

theorem acceleratedCapGradientY_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖acceleratedCapGradientY n k δ u y - acceleratedCapGradientY n k δ u z‖ ≤ 10040 * ‖y - z‖ := by
  by_cases hy : 2 * acceleratedDualRadius n k ≤ ‖y‖
  · by_cases hz : 2 * acceleratedDualRadius n k ≤ ‖z‖
    · rw [acceleratedCapGradientY_exterior hn hδ u y hy, acceleratedCapGradientY_exterior hn hδ u z hz,
        nonnegative_smul_difference (by norm_num : (0 : ℝ) ≤ 40)]
      exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
    · simpa only [norm_sub_rev] using acceleratedCapGradientY_difference_y_from_ball hn hδ u z y (le_of_not_ge hz)
  · exact acceleratedCapGradientY_difference_y_from_ball hn hδ u y z (le_of_not_ge hy)

end FreshGradientMinimax

