import FreshGradientMinimax.CoreTruncationResidual
import FreshGradientMinimax.PrimalModel

/-! Fixed-index truncated NC-SC models and their true joint-gradient
residuals after primal compression. The index is held fixed when differentiating. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def primalInteractionScale (L ε μ : ℝ) : ℝ :=
  2 * μ * Real.sqrt (primalValueScale L ε / μ)

theorem primalInteractionScale_pos {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) :
    0 < primalInteractionScale L ε μ :=
  mul_pos (mul_pos (by norm_num) hμ) (Real.sqrt_pos.mpr (div_pos (primalValueScale_pos hL hε) hμ))

theorem primalInteractionScale_paper {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) :
    primalInteractionScale L ε μ = 2 * Real.sqrt (μ * primalValueScale L ε) := by
  rw [primalInteractionScale, mul_assoc, coreScale_amplitude hμ (primalValueScale_pos hL hε).le]

theorem primalLengthScale_le_coreScale {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) :
    primalLengthScale L ε ≤ Real.sqrt (primalValueScale L ε / μ) := by
  have hr := primalLengthScale_pos hL hε
  have hlam := primalValueScale_pos hL hε
  rw [← primalScale_ratio hL hε] at hm
  have hs := (le_div_iff₀ (sq_pos_of_pos hr)).mp hm
  apply (sq_le_sq₀ hr.le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg hlam.le hμ.le)]
  exact (le_div_iff₀ hμ).mpr (by nlinarith only [hs])

variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)

def paperTruncatedModel {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (j : ℕ) : NCObjective dx dy L μ :=
  scaledCompressedModel U hL hε hμ hm
    (paperTruncatedCore_derivative_bounds V hμ (primalValueScale_pos hL hε) j)
    (paperTruncatedCore_strongConcave V hμ (primalValueScale_pos hL hε) j)

theorem paperTruncatedModel_gradient_residual {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (k : Fin (n + 1)) (x : Euclid dx) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k.val ≤ e.val →
      |frameCoordinates V y (e.castAdd n)| ≤ primalLengthScale L ε ∧
      |frameCoordinates V y (e.natAdd n)| ≤ primalLengthScale L ε) :
    ‖(paperCompressedModel U V hL hε hμ hm).gradX x y -
      (paperTruncatedModel U V hL hε hμ hm (k.val + 1)).gradX x y‖ ≤ 162 * primalInteractionScale L ε μ ∧
    ‖(paperCompressedModel U V hL hε hμ hm).gradY x y -
      (paperTruncatedModel U V hL hε hμ hm (k.val + 1)).gradY x y‖ ≤ 10 * primalInteractionScale L ε μ := by
  have hr := primalLengthScale_pos hL hε
  have h := paperCore_gradient_residual V hμ (primalValueScale_pos hL hε) hr.le
    (primalLengthScale_le_coreScale hL hε hμ hm) k
    (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x) y hu hy
  constructor
  · change ‖compressedGradX U _ _ _ _ x y - compressedGradX U _ _ _ _ x y‖ ≤ _
    simp only [compressedGradX, add_sub_add_right_eq_sub]
    calc
      _ ≤ (primalLengthScale L ε)⁻¹ * ‖gradient
          (fun u => paperCoreObjective V μ (primalValueScale L ε) u y)
          (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x) -
        gradient (fun u => paperTruncatedCore V μ (primalValueScale L ε) (k.val + 1) u y)
          (compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x)‖ :=
        compressedPullback_sub_gradient U hr _ x _ _
      _ ≤ (primalLengthScale L ε)⁻¹ * (162 * primalInteractionScale L ε μ * primalLengthScale L ε) :=
        mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hr.le)
      _ = _ := by field_simp
  · exact h.2

theorem paperTruncatedModel_joint_residual {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (k : Fin (n + 1)) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k.val ≤ e.val →
      |frameCoordinates V z.2 (e.castAdd n)| ≤ primalLengthScale L ε ∧
      |frameCoordinates V z.2 (e.natAdd n)| ≤ primalLengthScale L ε) :
    jointNormSq ((paperCompressedModel U V hL hε hμ hm).jointGradient z -
      (paperTruncatedModel U V hL hε hμ hm (k.val + 1)).jointGradient z) ≤
      (10 ^ 4 * primalInteractionScale L ε μ) ^ 2 := by
  have h := paperTruncatedModel_gradient_residual U V hL hε hμ hm k z.1 z.2 hu hy
  have hX := pow_le_pow_left₀ (norm_nonneg _) h.1 2
  have hY := pow_le_pow_left₀ (norm_nonneg _) h.2 2
  simp only [jointNormSq, Prod.fst_sub, Prod.snd_sub, NCObjective.jointGradient]
  nlinarith only [hX, hY, sq_nonneg (primalInteractionScale L ε μ)]

end FreshGradientMinimax
