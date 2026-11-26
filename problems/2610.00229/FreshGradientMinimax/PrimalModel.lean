import FreshGradientMinimax.CompressedSmoothness
import FreshGradientMinimax.PrimalParameters
import FreshGradientMinimax.CoreProtectionLemma

/-! The actual NC-SC model (26), with smoothness and strong concavity proved
from the displayed formulas and parameter choices. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)

theorem primal_parameters_mu_le_L {L μ : ℝ} (hL : 0 < L)
    (hm : μ ≤ L / (4 * primalScalingConstant)) : μ ≤ L := by
  unfold primalScalingConstant at hm
  linarith only [hm, hL]

def scaledCompressedModel {f : Euclid (n + 1) → Euclid dy → ℝ} {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (hf : CoreDerivativeBounds f (primalValueScale L ε) μ)
    (hsc : ∀ u, StrongConcaveGradient (f u) (gradient (f u)) μ) : NCObjective dx dy L μ where
  μ_pos := hμ
  μ_le_L := primal_parameters_mu_le_L hL hm
  f := compressedObjective U f (primalLengthScale L ε) (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε)
  gradX := compressedGradX U f (primalLengthScale L ε) (primalCompressionRadius n L ε) (primalRidgeCoefficient L ε)
  gradY := compressedGradY U f (primalLengthScale L ε) (primalCompressionRadius n L ε)
  derivative := compressedObjective_hasFDerivAt U f (primalCompressionRadius_pos n hL hε) hf.joint_contDiff
  joint_smooth := by
    have hr := primalLengthScale_pos hL hε
    have hR := primalCompressionRadius_pos n hL hε
    have hxx := primalScale_xx_bound n hL hε
    have hxy := primalScale_xy_bound hL hε hμ.le hm
    have hyy := primalScale_yy_bound hL hm
    have hxx' : _ ≤ L / 2 := hxx.trans (by linarith only [hL])
    have hxy' : _ ≤ L / 2 := hxy.trans (by linarith only [hL])
    have hyy' : _ ≤ L / 2 := hyy.trans (by linarith only [hL])
    intro x y z w
    apply joint_smooth_of_four_blocks hL.le
    · intro a b c
      exact (compressedGradX_sub_x U hr hR (primalRidgeCoefficient_pos hL hε).le
        (primalValueScale_pos hL hε).le hf a b c).trans (mul_le_mul_of_nonneg_right hxx' (norm_nonneg _))
    · intro a b c
      exact (compressedGradX_sub_y U hr hf a b c).trans (mul_le_mul_of_nonneg_right hxy' (norm_nonneg _))
    · intro a b c
      exact (compressedGradY_sub_x U hr hR hf a b c).trans (mul_le_mul_of_nonneg_right hxy' (norm_nonneg _))
    · intro a b c
      exact (compressedGradY_sub_y U hf a b c).trans (mul_le_mul_of_nonneg_right hyy' (norm_nonneg _))
  dual_strong := compressedObjective_strongConcave U f hsc

def paperCompressedModel (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) : NCObjective dx dy L μ :=
  scaledCompressedModel U hL hε hμ hm (paperCore_derivative_bounds V hμ (primalValueScale_pos hL hε))
    (core_C2_strongConcave V hμ (primalValueScale_pos hL hε))

theorem paperCompressedModel_dual_zero (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) :
    (paperCompressedModel U V hL hε hμ hm).gradY 0 0 = 0 := by
  change gradient (paperCoreObjective V μ (primalValueScale L ε)
    (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) 0)) 0 = 0
  rw [compressedCoordinates_zero]
  exact core_C2_gradient_y_zero V hμ (primalValueScale_pos hL hε)

theorem paperCompressedModel_localized_zero (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) :
    (paperCompressedModel U V hL hε hμ hm).DualLocalized 0 := by
  change ‖(paperCompressedModel U V hL hε hμ hm).gradY 0 0‖ ≤ 0
  rw [paperCompressedModel_dual_zero U V hL hε hμ hm, norm_zero]

end FreshGradientMinimax
