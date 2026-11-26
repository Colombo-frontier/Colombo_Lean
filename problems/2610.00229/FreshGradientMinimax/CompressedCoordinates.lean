import FreshGradientMinimax.RadialCompression
import FreshGradientMinimax.CoreCertificate

/-! Compressed frame coordinates and their true adjoint differential. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)

def compressedCoordinates (r R : ℝ) (x : Euclid dx) : Euclid m :=
  r⁻¹ • frameCoordinates U (radialCompression R x)

def compressedCoordinatesDerivative (r R : ℝ) (x : Euclid dx) : Euclid dx →L[ℝ] Euclid m :=
  r⁻¹ • (frameCoordinates U).comp (radialCompressionDerivative R x)

def compressedPullback (r R : ℝ) (x : Euclid dx) (g : Euclid m) : Euclid dx :=
  r⁻¹ • radialCompressionDerivative R x (U g)

theorem compressedCoordinates_hasFDerivAt (r : ℝ) {R : ℝ} (hR : 0 < R) (x : Euclid dx) :
    HasFDerivAt (compressedCoordinates U r R) (compressedCoordinatesDerivative U r R x) x :=
  (((frameCoordinates U).hasFDerivAt).comp x (radialCompression_hasFDerivAt hR x)).const_smul r⁻¹

theorem compressedPullback_inner (r R : ℝ) (x v : Euclid dx) (g : Euclid m) :
    ⟪compressedPullback U r R x g, v⟫_ℝ = ⟪g, compressedCoordinatesDerivative U r R x v⟫_ℝ := by
  simp only [compressedPullback, compressedCoordinatesDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, real_inner_smul_left, inner_smul_right,
    radialCompressionDerivative_selfAdjoint, frameCoordinates,
    ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]

theorem compressedCoordinates_contDiff {k : ℕ∞} (r R : ℝ) :
    ContDiff ℝ k (compressedCoordinates U r R) :=
  ((frameCoordinates U).contDiff.comp (radialCompression_contDiff R)).const_smul r⁻¹

theorem compressedCoordinates_sub_norm {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (x z : Euclid dx) :
    ‖compressedCoordinates U r R x - compressedCoordinates U r R z‖ ≤ r⁻¹ * ‖x - z‖ := by
  simp only [compressedCoordinates, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left
    ((frameCoordinates_norm_bound U _).trans (radialCompression_sub_norm hR x z)) (inv_nonneg.mpr hr.le)

theorem compressedCoordinates_norm_bound {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (x : Euclid dx) :
    ‖compressedCoordinates U r R x‖ ≤ R / r := by
  rw [compressedCoordinates, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left
    ((frameCoordinates_norm_bound U _).trans (radialCompression_norm_bound hR x)) (inv_nonneg.mpr hr.le)

theorem compressedCoordinates_zero (r R : ℝ) : compressedCoordinates U r R 0 = 0 := by
  simp only [compressedCoordinates, radialCompression_zero, map_zero, smul_zero]

theorem compressedPullback_norm {r : ℝ} (hr : 0 < r) (R : ℝ) (x : Euclid dx) (g : Euclid m) :
    ‖compressedPullback U r R x g‖ ≤ r⁻¹ * ‖g‖ := by
  rw [compressedPullback, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [U.norm_map] using radialCompressionDerivative_norm_apply (R := R) x (U g))
    (inv_nonneg.mpr hr.le)

theorem compressedPullback_sub_gradient {r : ℝ} (hr : 0 < r) (R : ℝ)
    (x : Euclid dx) (g h : Euclid m) :
    ‖compressedPullback U r R x g - compressedPullback U r R x h‖ ≤ r⁻¹ * ‖g - h‖ := by
  simpa only [compressedPullback, map_sub, smul_sub] using compressedPullback_norm U hr R x (g - h)

theorem compressedPullback_sub_point {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (x z : Euclid dx) (g : Euclid m) :
    ‖compressedPullback U r R x g - compressedPullback U r R z g‖ ≤
      (3 / (r * R)) * ‖x - z‖ * ‖g‖ := by
  have h1 := (radialCompressionDerivative R x - radialCompressionDerivative R z).le_opNorm (U g)
  have h2 := mul_le_mul_of_nonneg_right (radialCompressionDerivative_sub_norm hR x z) (norm_nonneg (U g))
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.mpr hr.le)
  simp only [ContinuousLinearMap.sub_apply, U.norm_map] at h3
  rw [compressedPullback, compressedPullback, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  convert h3 using 1
  field_simp

end FreshGradientMinimax
