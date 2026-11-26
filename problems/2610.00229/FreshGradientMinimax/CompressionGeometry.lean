import FreshGradientMinimax.CompressedCoordinates

/-! Scalar and coordinate formulas for the compression used in the barrier. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radialCompression_eq_factor {R : ℝ} (hR : 0 < R) (x : E) :
    radialCompression R x = compressionFactor (R⁻¹ • x) • x := by
  unfold radialCompression unitCompression
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

theorem radialCompressionDerivative_formula {R : ℝ} (_hR : 0 < R) (x v : E) :
    radialCompressionDerivative R x v = compressionFactor (R⁻¹ • x) • v -
      (compressionFactor (R⁻¹ • x) ^ 3 / R ^ 2 * ⟪x, v⟫_ℝ) • x := by
  rw [radialCompressionDerivative, unitCompressionDerivative_apply]
  simp only [real_inner_smul_left, smul_smul]
  congr 2
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem compressionFactor_lower_half_ball {R : ℝ} (hR : 0 < R) (x : E) (hx : ‖x‖ ≤ R / 2) :
    4 / 5 ≤ compressionFactor (R⁻¹ • x) := by
  have hn : ‖R⁻¹ • x‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, ← div_eq_inv_mul]
    exact (div_le_iff₀ hR).mpr (by linarith only [hx])
  have ha := compressionFactor_pos (R⁻¹ • x)
  have hid := compressionFactor_identity (R⁻¹ • x)
  have hsq : ‖R⁻¹ • x‖ ^ 2 ≤ 1 / 4 := by nlinarith only [hn, norm_nonneg (R⁻¹ • x)]
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (compressionFactor (R⁻¹ • x)))
  nlinarith only [hid, hm, ha, sq_nonneg (compressionFactor (R⁻¹ • x) - 4 / 5)]

theorem compressedCoordinates_unit_formula {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (x : Euclid dx) :
    compressedCoordinates U 1 R x = compressionFactor (R⁻¹ • x) • frameCoordinates U x := by
  simp only [compressedCoordinates, inv_one, one_smul, radialCompression_eq_factor hR, map_smul]

theorem compressed_small_coordinate {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (x : Euclid dx) (hx : ‖x‖ ≤ R / 2) (j : Fin m)
    (hj : |compressedCoordinates U 1 R x j| ≤ 1) : |frameCoordinates U x j| ≤ 5 / 4 := by
  rw [compressedCoordinates_unit_formula U hR, PiLp.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (compressionFactor_pos _)] at hj
  have hl := mul_le_mul_of_nonneg_right (compressionFactor_lower_half_ball hR x hx) (abs_nonneg (frameCoordinates U x j))
  linarith only [hl, hj]

theorem compressed_gradient_coordinate {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (x : Euclid dx) (g : Euclid m) (j : Fin m) :
    frameCoordinates U (radialCompressionDerivative R x (U g) + η • x) j =
      compressionFactor (R⁻¹ • x) * g j -
      (compressionFactor (R⁻¹ • x) ^ 3 / R ^ 2 * ⟪x, U g⟫_ℝ) * frameCoordinates U x j +
      η * frameCoordinates U x j := by
  simp only [radialCompressionDerivative_formula hR, map_add, map_sub, map_smul,
    frameCoordinates_frame, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]

end FreshGradientMinimax
