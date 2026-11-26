import FreshGradientMinimax.CompressionBarrier
import FreshGradientMinimax.CompressedPrimalValue

/-! Transfer the normalized barrier back to the original physical scale. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
variable {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)

theorem radialCompression_rescale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r P : ℝ) (x : E) : radialCompression (r * P) x = r • radialCompression P (r⁻¹ • x) := by
  simp only [radialCompression, mul_inv_rev, smul_smul]

theorem radialCompressionDerivative_rescale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r P : ℝ) (x : E) : radialCompressionDerivative (r * P) x = radialCompressionDerivative P (r⁻¹ • x) := by
  simp only [radialCompressionDerivative, mul_inv_rev, smul_smul]

theorem compressedCoordinates_rescale {r : ℝ} (hr : 0 < r) (P : ℝ) (x : Euclid dx) :
    compressedCoordinates U r (r * P) x = compressedCoordinates U 1 P (r⁻¹ • x) := by
  simp only [compressedCoordinates, radialCompression_rescale, map_smul, smul_smul,
    inv_mul_cancel₀ hr.ne', inv_one, one_smul]

theorem compressedCoreGradient_rescale {r : ℝ} (hr : 0 < r) (lam P η : ℝ) (x : Euclid dx) :
    compressedCoreGradient U lam r (r * P) (lam * η / r ^ 2) x =
      (lam / r) • normalizedCoreGradient U P η (r⁻¹ • x) := by
  simp only [compressedCoreGradient, compressedPullback, compressedCoordinates_rescale U hr,
    radialCompressionDerivative_rescale, normalizedCoreGradient, smul_add, smul_smul,
    div_eq_mul_inv, inv_pow]
  congr 1
  congr 1
  ring

theorem compressedCoreGradient_barrier {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (x : Euclid dx)
    (hlast : |compressedCoordinates U r (r * (primalRadiusConstant * Real.sqrt (n + 1 : ℝ))) x (Fin.last n)| ≤ 1 / 4) :
    (lam / r) * (primalBarrierConstant / 2) ≤
      ‖compressedCoreGradient U lam r (r * (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)))
        (lam * primalRidgeConstant / r ^ 2) x‖ := by
  rw [compressedCoordinates_rescale U hr] at hlast
  rw [compressedCoreGradient_rescale U hr, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlam hr.le)]
  exact mul_le_mul_of_nonneg_left (normalizedCoreGradient_barrier U (r⁻¹ • x) hlast) (div_nonneg hlam hr.le)

theorem paperCompressedModel_barrier {dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant)) (x : Euclid dx)
    (hlast : |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) x (Fin.last n)| ≤ 1 / 4) :
    2 * ε ≤ ‖(paperCompressedModel U V hL hε hμ hm).primalGradient x‖ := by
  have hR : primalCompressionRadius n L ε = primalLengthScale L ε * (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) := by
    unfold primalCompressionRadius
    ring
  rw [hR] at hlast
  rw [paperCompressedModel_primalGradient U V hL hε hμ hm, hR, primalRidgeCoefficient]
  have h := compressedCoreGradient_barrier U (primalLengthScale_pos hL hε) (primalValueScale_pos hL hε).le x hlast
  have he : primalValueScale L ε / primalLengthScale L ε * (primalBarrierConstant / 2) = 2 * ε := by
    rw [primalScale_gradient_ratio hL hε]
    field_simp [primalBarrierConstant_pos.ne']
    ring
  rw [he] at h
  exact h

end FreshGradientMinimax
