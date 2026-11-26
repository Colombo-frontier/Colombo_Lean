import FreshGradientMinimax.CompressionGeometry
import FreshGradientMinimax.AcceleratedCompressionParameters

/-! Exact projected-gradient formula and explicit bounds for its ridge
coefficient. The estimates use the full ambient query norm. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)

def compressedRidgeFactor (R η : ℝ) (x : Euclid dx) (g : Euclid m) : ℝ :=
  η / compressionFactor (R⁻¹ • x) - compressionFactor (R⁻¹ • x) *
    ⟪compressedCoordinates U 1 R x, g⟫_ℝ / R ^ 2

theorem compressedRidgeFactor_coordinate {R : ℝ} (hR : 0 < R) (η : ℝ)
    (x : Euclid dx) (g : Euclid m) (j : Fin m) :
    frameCoordinates U (radialCompressionDerivative R x (U g) + η • x) j =
      compressionFactor (R⁻¹ • x) * g j +
        compressedRidgeFactor U R η x g * compressedCoordinates U 1 R x j := by
  rw [compressed_gradient_coordinate U hR, compressedRidgeFactor, compressedCoordinates_unit_formula U hR]
  have hi : ⟪frameCoordinates U x, g⟫_ℝ = ⟪x, U g⟫_ℝ := by
    exact U.toContinuousLinearMap.adjoint_inner_left g x
  simp only [real_inner_smul_left, PiLp.smul_apply, smul_eq_mul, hi]
  have ha := (compressionFactor_pos (R⁻¹ • x)).ne'
  generalize compressionFactor (R⁻¹ • x) = a at *
  field_simp [ha, hR.ne']
  ring

theorem compressedRidgeFactor_correction_bound {R : ℝ} (hR : 0 < R)
    (x : Euclid dx) (g : Euclid m) :
    |compressionFactor (R⁻¹ • x) * ⟪compressedCoordinates U 1 R x, g⟫_ℝ / R ^ 2| ≤ ‖g‖ / R := by
  have hu := compressedCoordinates_norm_bound U (by norm_num : (0 : ℝ) < 1) hR.le x
  rw [div_one] at hu
  have hi := (abs_real_inner_le_norm (compressedCoordinates U 1 R x) g).trans
    (mul_le_mul_of_nonneg_right hu (norm_nonneg g))
  have ha := compressionFactor_pos (R⁻¹ • x)
  have h := mul_le_mul (compressionFactor_le_one (R⁻¹ • x)) hi (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [one_mul] at h
  rw [abs_div, abs_mul, abs_of_pos ha, abs_of_nonneg (sq_nonneg R)]
  refine (div_le_div_of_nonneg_right h (sq_nonneg R)).trans_eq ?_
  field_simp
  ring

theorem acceleratedRidgeFactor_bounds {k : ℕ}
    (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx) (x : Euclid dx) (g : Euclid (k * 2 + 1))
    (hx : ‖x‖ ≤ acceleratedPrimalRadius k / 2) (hg : ‖g‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ)) :
    (9 / 10) * primalRidgeConstant ≤ compressedRidgeFactor U (acceleratedPrimalRadius k) primalRidgeConstant x g ∧
    compressedRidgeFactor U (acceleratedPrimalRadius k) primalRidgeConstant x g ≤ (13 / 10) * primalRidgeConstant := by
  let R := acceleratedPrimalRadius k
  let a := compressionFactor (R⁻¹ • x)
  have hR : 0 < R := acceleratedPrimalRadius_pos k
  have ha : 0 < a := compressionFactor_pos _
  have ha1 : a ≤ 1 := compressionFactor_le_one _
  have ha0 : 4 / 5 ≤ a := compressionFactor_lower_half_ball hR x hx
  have he : (10 ^ 8 * Real.sqrt (k + 1 : ℕ)) / R = primalRidgeConstant / 10 ^ 4 := by
    have hc := accelerated_radius_correction k
    change 3 * (10 ^ 8 * Real.sqrt (k + 1 : ℕ)) / R = _ at hc
    linear_combination hc / 3
  have hc := (compressedRidgeFactor_correction_bound U hR x g).trans
    (div_le_div_of_nonneg_right hg hR.le)
  rw [he] at hc
  have hηlo : primalRidgeConstant ≤ primalRidgeConstant / a :=
    (le_div_iff₀ ha).mpr (by nlinarith only [ha1, primalRidgeConstant_pos])
  have hηhi : primalRidgeConstant / a ≤ (5 / 4) * primalRidgeConstant :=
    (div_le_iff₀ ha).mpr (by nlinarith only [ha0, primalRidgeConstant_pos])
  change (9 / 10) * primalRidgeConstant ≤ primalRidgeConstant / a -
    a * ⟪compressedCoordinates U 1 R x, g⟫_ℝ / R ^ 2 ∧
    primalRidgeConstant / a - a * ⟪compressedCoordinates U 1 R x, g⟫_ℝ / R ^ 2 ≤ (13 / 10) * primalRidgeConstant
  have hc' := abs_le.mp hc
  constructor <;> nlinarith only [hηlo, hηhi, hc'.1, hc'.2, primalRidgeConstant_pos]

end FreshGradientMinimax

