import FreshGradientMinimax.AcceleratedEndgame
import FreshGradientMinimax.CoordinateScaledValue
import FreshGradientMinimax.AcceleratedPhysicalParameters

/-! The original accelerated hard objective in physical coordinates. The
model retains L/2 smoothness, at least 2 mu strong concavity, and G0 = 0. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n k dx dy : ℕ}
  (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
  (hn : 10 ≤ n + 2) (hk : 0 < k)
  {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
  (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ))

def acceleratedPhysicalModel : NCObjective dx dy L μ :=
  (coordinateScaledModel (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
    (acceleratedValueScale_pos hL hε) (acceleratedLengthScale_pos hL hε)).weakenConstants
    (by rw [acceleratedScale_smoothness hL hε]; linarith only [hL]) hμ
    (by have h := acceleratedScale_strongConcavity hL hε hμ hchain; linarith only [h, hμ])

theorem acceleratedPhysicalModel_formula (x : Euclid dx) (y : Euclid dy) :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).f x y =
      acceleratedValueScale L ε * acceleratedCompressedObjective U V (acceleratedThreshold n k)
        ((acceleratedLengthScale L ε)⁻¹ • x) ((acceleratedLengthScale L ε)⁻¹ • y) := rfl

theorem acceleratedPhysicalModel_smooth_half (x z : Euclid dx) (y w : Euclid dy) :
    ‖(acceleratedPhysicalModel U V hn hk hL hε hμ hchain).gradX x y -
        (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).gradX z w‖ ^ 2 +
      ‖(acceleratedPhysicalModel U V hn hk hL hε hμ hchain).gradY x y -
        (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).gradY z w‖ ^ 2 ≤
      (L / 2) ^ 2 * (‖x - z‖ ^ 2 + ‖y - w‖ ^ 2) := by
  have h := coordinateScaledGrad_joint_smooth (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
    (acceleratedValueScale L ε) (acceleratedLengthScale L ε) x z y w
  rw [acceleratedScale_smoothness hL hε] at h
  exact h

theorem acceleratedPhysicalModel_strong_twice (x : Euclid dx) :
    StrongConcaveGradient ((acceleratedPhysicalModel U V hn hk hL hε hμ hchain).f x)
      ((acceleratedPhysicalModel U V hn hk hL hε hμ hchain).gradY x) (2 * μ) := by
  intro y z
  have h := coordinateScaledFunction_strongConcave
    (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
    (acceleratedValueScale_pos hL hε).le (acceleratedLengthScale L ε) x y z
  have hm := mul_le_mul_of_nonneg_right (acceleratedScale_strongConcavity hL hε hμ hchain) (sq_nonneg ‖z - y‖)
  change coordinateScaledFunction _ _ _ x z ≤ coordinateScaledFunction _ _ _ x y +
    ⟪coordinateScaledGradY (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
      (acceleratedValueScale L ε) (acceleratedLengthScale L ε) x y, z - y⟫_ℝ - (2 * μ) / 2 * ‖z - y‖ ^ 2
  linarith only [h, hm]

theorem acceleratedPhysicalModel_localized :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).DualLocalized 0 := by
  have h := coordinateScaledModel_localized
    (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
    (acceleratedValueScale_pos hL hε) (acceleratedLengthScale_pos hL hε)
    (acceleratedCompressedModel_localized U V hn (acceleratedThreshold_pos n hk).le)
  simpa only [mul_zero] using h

theorem acceleratedPhysicalModel_origin_dual :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).dualMax 0 = 0 := by
  have h := (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).initial_dual_distance
    (acceleratedPhysicalModel_localized U V hn hk hL hε hμ hchain)
  rw [zero_div] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem acceleratedPhysicalModel_value (x : Euclid dx) :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).value x =
      acceleratedValueScale L ε * acceleratedCompressedValue U V (acceleratedThreshold n k)
        ((acceleratedLengthScale L ε)⁻¹ • x) := by
  unfold acceleratedPhysicalModel
  rw [NCObjective.weakenConstants_value, coordinateScaledModel_value, acceleratedCompressedModel_value]

theorem acceleratedPhysicalModel_gap {Δ : ℝ}
    (hgap : 1000 * (k + 1 : ℕ) * acceleratedValueScale L ε ≤ Δ) :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).PrimalGapAtMost Δ := by
  have h := coordinateScaledModel_gap
    (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le)
    (acceleratedValueScale_pos hL hε) (acceleratedLengthScale_pos hL hε)
    (acceleratedCompressedModel_gap U V hn hk)
  intro x
  exact (h x).trans (by nlinarith only [hgap])

theorem acceleratedPhysicalModel_primalGradient (x : Euclid dx) :
    (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).primalGradient x =
      (acceleratedValueScale L ε / acceleratedLengthScale L ε) •
        (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le).primalGradient
          ((acceleratedLengthScale L ε)⁻¹ • x) := by
  unfold acceleratedPhysicalModel
  rw [NCObjective.weakenConstants_primalGradient, coordinateScaledModel_primalGradient]

theorem acceleratedPhysicalModel_barrier (x : Euclid dx)
    (hlast : |compressedCoordinates U 1 (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • x)
      (interleavedZ (⟨k - 1, by omega⟩ : Fin k))| ≤ 1 / 4) :
    2 * ε ≤ ‖(acceleratedPhysicalModel U V hn hk hL hε hμ hchain).primalGradient x‖ := by
  have h := lemma_E2 U V hn hk ((acceleratedLengthScale L ε)⁻¹ • x) hlast
  rw [NCObjective.true_primal_gradient] at h
  rw [acceleratedPhysicalModel_primalGradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (acceleratedValueScale_pos hL hε) (acceleratedLengthScale_pos hL hε))]
  have hh := mul_le_mul_of_nonneg_left h (div_pos (acceleratedValueScale_pos hL hε) (acceleratedLengthScale_pos hL hε)).le
  have he : acceleratedValueScale L ε / acceleratedLengthScale L ε * (primalRidgeConstant / 2) = 2 * ε := by
    rw [acceleratedScale_gradient_ratio hL hε]
    field_simp [primalRidgeConstant_pos.ne']
    ring
  rwa [he] at hh

end FreshGradientMinimax
