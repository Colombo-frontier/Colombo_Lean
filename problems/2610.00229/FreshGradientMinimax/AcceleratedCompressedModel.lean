import FreshGradientMinimax.AcceleratedGlobalLemma
import FreshGradientMinimax.GeneralCompressedSmoothness
import FreshGradientMinimax.AcceleratedCompressionParameters

/-! The actual normalized model (39), with both arbitrary ambient frames,
the paper's primal radius and its original smoothness constant. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n k dx dy : ℕ}
  (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

theorem framedAcceleratedProtected_gradient_u {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    gradient (fun v => framedAcceleratedProtected V δ v y) u = framedAcceleratedGradientU V δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (framedAcceleratedProtected_hasFDerivAt_u V hδ u y)).gradient

theorem framedAcceleratedProtected_gradient_y {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    gradient (framedAcceleratedProtected V δ u) y = framedAcceleratedGradientY V δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (framedAcceleratedProtected_hasFDerivAt_y V hδ u y)).gradient

def acceleratedCompressedObjective (δ : ℝ) : Euclid dx → Euclid dy → ℝ :=
  compressedObjective U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k) primalRidgeConstant

def acceleratedCompressedGradX (δ : ℝ) : Euclid dx → Euclid dy → Euclid dx :=
  compressedGradX U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k) primalRidgeConstant

def acceleratedCompressedGradY (δ : ℝ) : Euclid dx → Euclid dy → Euclid dy :=
  compressedGradY U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k)

theorem acceleratedCompressedGradX_sub_x (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (x z : Euclid dx) (y : Euclid dy) :
    ‖acceleratedCompressedGradX U V δ x y - acceleratedCompressedGradX U V δ z y‖ ≤
      acceleratedSmoothnessConstant / 2 * ‖x - z‖ := by
  have hxx : ∀ u v y, ‖gradient (fun w => framedAcceleratedProtected V δ w y) u -
      gradient (fun w => framedAcceleratedProtected V δ w y) v‖ ≤ 10 ^ 8 * ‖u - v‖ := by
    intro u v y
    simp only [framedAcceleratedProtected_gradient_u V hδ]
    exact (framedAcceleratedModel V hn hδ).gradX_lip_primal u v y
  have hb : ∀ u y, ‖gradient (fun w => framedAcceleratedProtected V δ w y) u‖ ≤
      10 ^ 8 * Real.sqrt (k + 1 : ℕ) := by
    intro u y
    rw [framedAcceleratedProtected_gradient_u V hδ]
    exact framedAcceleratedModel_gradient_bound V hn hδ u y
  have h := compressedGradX_sub_x_general U (by norm_num : (0 : ℝ) < 1)
    (acceleratedPrimalRadius_pos k) primalRidgeConstant_pos.le (by norm_num) hxx hb x z y
  simp only [one_pow, div_one, one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right (accelerated_compression_xx_bound k) (norm_nonneg _))

theorem acceleratedCompressedGradX_sub_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖acceleratedCompressedGradX U V δ x y - acceleratedCompressedGradX U V δ x z‖ ≤
      acceleratedSmoothnessConstant / 2 * ‖y - z‖ := by
  have hxy : ∀ u y z, ‖gradient (fun w => framedAcceleratedProtected V δ w y) u -
      gradient (fun w => framedAcceleratedProtected V δ w z) u‖ ≤ 10 ^ 8 * ‖y - z‖ := by
    intro u y z
    simp only [framedAcceleratedProtected_gradient_u V hδ]
    exact (framedAcceleratedModel V hn hδ).gradX_lip_dual u y z
  have h := compressedGradX_sub_y_general U (R := acceleratedPrimalRadius k)
    (β := primalRidgeConstant) (by norm_num : (0 : ℝ) < 1) hxy x y z
  rw [div_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right accelerated_compression_other_bound (norm_nonneg _))

theorem acceleratedCompressedGradY_sub_x (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (x z : Euclid dx) (y : Euclid dy) :
    ‖acceleratedCompressedGradY U V δ x y - acceleratedCompressedGradY U V δ z y‖ ≤
      acceleratedSmoothnessConstant / 2 * ‖x - z‖ := by
  have hyx : ∀ u v y, ‖gradient (framedAcceleratedProtected V δ u) y -
      gradient (framedAcceleratedProtected V δ v) y‖ ≤ 10 ^ 8 * ‖u - v‖ := by
    intro u v y
    simp only [framedAcceleratedProtected_gradient_y V hδ]
    exact (framedAcceleratedModel V hn hδ).gradY_lip_primal u v y
  have h := compressedGradY_sub_x_general U (by norm_num : (0 : ℝ) < 1)
    (acceleratedPrimalRadius_pos k) (by norm_num) hyx x z y
  rw [div_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right accelerated_compression_other_bound (norm_nonneg _))

theorem acceleratedCompressedGradY_sub_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖acceleratedCompressedGradY U V δ x y - acceleratedCompressedGradY U V δ x z‖ ≤
      acceleratedSmoothnessConstant / 2 * ‖y - z‖ := by
  have hyy : ∀ u y z, ‖gradient (framedAcceleratedProtected V δ u) y -
      gradient (framedAcceleratedProtected V δ u) z‖ ≤ 10 ^ 8 * ‖y - z‖ := by
    intro u y z
    simp only [framedAcceleratedProtected_gradient_y V hδ]
    exact (framedAcceleratedModel V hn hδ).gradY_lip_dual u y z
  exact (compressedGradY_sub_y_general U (r := 1) (R := acceleratedPrimalRadius k) hyy x y z).trans
    (mul_le_mul_of_nonneg_right accelerated_compression_other_bound (norm_nonneg _))

def acceleratedCompressedModel (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    NCObjective dx dy acceleratedSmoothnessConstant (robinStep (n + 2) ^ 2) where
  μ_pos := sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))
  μ_le_L := (robinStep_sq_le_one n).trans (by norm_num [acceleratedSmoothnessConstant])
  f := acceleratedCompressedObjective U V δ
  gradX := acceleratedCompressedGradX U V δ
  gradY := acceleratedCompressedGradY U V δ
  derivative := compressedObjective_hasFDerivAt U _ (acceleratedPrimalRadius_pos k)
    (framedAcceleratedProtected_joint_contDiff V hδ)
  joint_smooth := by
    intro x y z w
    exact joint_smooth_of_four_blocks (by norm_num [acceleratedSmoothnessConstant])
      (acceleratedCompressedGradX_sub_x U V hn hδ) (acceleratedCompressedGradX_sub_y U V hn hδ)
      (acceleratedCompressedGradY_sub_x U V hn hδ) (acceleratedCompressedGradY_sub_y U V hn hδ) x z y w
  dual_strong := by
    apply compressedObjective_strongConcave
    intro u y z
    simpa only [framedAcceleratedProtected_gradient_y V hδ] using
      framedAcceleratedProtected_strongConcave V hδ u y z

theorem acceleratedCompressedModel_localized (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (acceleratedCompressedModel U V hn hδ).DualLocalized 0 := by
  change ‖compressedGradY U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k) 0 0‖ ≤ 0
  simp only [compressedGradY, compressedCoordinates_zero, framedAcceleratedProtected_gradient_y V hδ,
    framedAcceleratedGradientY_origin V hδ, norm_zero, le_refl]

end FreshGradientMinimax

