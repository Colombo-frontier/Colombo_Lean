import FreshGradientMinimax.CompressionGeometry
import FreshGradientMinimax.PrimalParameters

/-! The normalized stationarity barrier, including arbitrary large outputs. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem compression_coordinate_correction_bound {m dx : ℕ} (U : Euclid m →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (x : Euclid dx) (g : Euclid m) (j : Fin m)
    (hx : ‖x‖ ≤ R / 2) (hj : |frameCoordinates U x j| ≤ 5 / 4) :
    |(compressionFactor (R⁻¹ • x) ^ 3 / R ^ 2 * ⟪x, U g⟫_ℝ) * frameCoordinates U x j| ≤ ‖g‖ / R := by
  have ha := (compressionFactor_pos (R⁻¹ • x)).le
  have ha3 : compressionFactor (R⁻¹ • x) ^ 3 ≤ 1 := pow_le_one₀ ha (compressionFactor_le_one _) 
  have hi : |⟪x, U g⟫_ℝ| ≤ R / 2 * ‖g‖ := by
    have hh := mul_le_mul_of_nonneg_right hx (norm_nonneg (U g))
    exact (abs_real_inner_le_norm x (U g)).trans (by simpa only [U.norm_map] using hh)
  have hc := div_le_div_of_nonneg_right ha3 (sq_nonneg R)
  have h1 := mul_le_mul hc hi (abs_nonneg _) (by positivity : 0 ≤ 1 / R ^ 2)
  have h2 := mul_le_mul h1 hj (abs_nonneg _) (by positivity : 0 ≤ 1 / R ^ 2 * (R / 2 * ‖g‖))
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ compressionFactor (R⁻¹ • x) ^ 3 / R ^ 2)]
  refine h2.trans ?_
  have he : 1 / R ^ 2 * (R / 2 * ‖g‖) * (5 / 4) = (5 / 8) * (‖g‖ / R) := by
    field_simp
    ring
  rw [he]
  nlinarith only [div_nonneg (norm_nonneg g) hR.le]

def normalizedCoreValue {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (R η : ℝ) (x : Euclid dx) : ℝ :=
  coreChain (compressedCoordinates U 1 R x) + η / 2 * ‖x‖ ^ 2

def normalizedCoreGradient {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (R η : ℝ) (x : Euclid dx) : Euclid dx :=
  radialCompressionDerivative R x (U (gradient coreChain (compressedCoordinates U 1 R x))) + η • x

theorem normalizedCoreValue_hasFDerivAt {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (x : Euclid dx) :
    HasFDerivAt (normalizedCoreValue U R η) (innerSL ℝ (normalizedCoreGradient U R η x)) x := by
  have hf := ((coreChain_contDiff (m := 1)).differentiable (by norm_num) (compressedCoordinates U 1 R x)).hasGradientAt.hasFDerivAt
  have hd := (hf.comp x (compressedCoordinates_hasFDerivAt U 1 hR x)).add (half_quadratic_hasFDerivAt η x)
  apply hd.congr_fderiv
  ext v
  have hp := compressedPullback_inner U 1 R x v (gradient coreChain (compressedCoordinates U 1 R x))
  simp only [compressedPullback, inv_one, one_smul] at hp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply, innerSL_apply, normalizedCoreGradient, inner_add_left, hp]

theorem normalizedCoreValue_gradient {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (x : Euclid dx) :
    gradient (normalizedCoreValue U R η) x = normalizedCoreGradient U R η x :=
  (hasGradientAt_iff_hasFDerivAt.mpr (normalizedCoreValue_hasFDerivAt U hR η x)).gradient

theorem normalizedCoreGradient_small_barrier {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (x : Euclid dx) (hx : ‖x‖ ≤ (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) / 2)
    (hlast : |compressedCoordinates U 1 (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) x (Fin.last n)| ≤ 1 / 4) :
    primalBarrierConstant / 2 ≤ ‖normalizedCoreGradient U (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) primalRidgeConstant x‖ := by
  let R := primalRadiusConstant * Real.sqrt (n + 1 : ℝ)
  let u := compressedCoordinates U 1 R x
  let g := gradient coreChain u
  have hR : 0 < R := mul_pos primalRadiusConstant_pos (Real.sqrt_pos.mpr (by positivity))
  obtain ⟨j, hj, hg⟩ := coreChain_coordinate_barrier u hlast
  have hj' := compressed_small_coordinate U hR x hx j hj
  have hc := compression_coordinate_correction_bound U hR x g j hx hj'
  have hn : ‖g‖ / R ≤ 10 ^ 6 / primalRadiusConstant := by
    apply (div_le_iff₀ hR).mpr
    have he : 10 ^ 6 / primalRadiusConstant * R = 10 ^ 6 * Real.sqrt (n + 1 : ℝ) := by
      dsimp only [R]
      field_simp [primalRadiusConstant_pos.ne']
      ring
    rw [he]
    exact coreChain_gradient_original_bound u
  have ha := compressionFactor_lower_half_ball hR x hx
  have hga := mul_le_mul_of_nonneg_left hg (compressionFactor_pos (R⁻¹ • x)).le
  change compressionFactor (R⁻¹ • x) * g j ≤ compressionFactor (R⁻¹ • x) * (-primalBarrierConstant) at hga
  have hga' := mul_le_mul_of_nonneg_right ha primalBarrierConstant_pos.le
  have hη := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hj') primalRidgeConstant_pos.le
  have hnum : 10 ^ 6 / primalRadiusConstant + primalRidgeConstant * (5 / 4) ≤ (3 / 10) * primalBarrierConstant := by
    unfold primalRadiusConstant primalRidgeConstant
    rw [div_div_eq_mul_div]
    nlinarith only [primalBarrierConstant_pos]
  have hcoord := compressed_gradient_coordinate U hR primalRidgeConstant x g j
  have hproj : frameCoordinates U (normalizedCoreGradient U R primalRidgeConstant x) j ≤ -primalBarrierConstant / 2 := by
    change frameCoordinates U (radialCompressionDerivative R x (U g) + primalRidgeConstant • x) j ≤ _
    rw [hcoord]
    have hb := (neg_le_abs _).trans (hc.trans hn)
    nlinarith only [hga, hga', hη, hnum, hb]
  have h1 := PiLp.norm_apply_le (frameCoordinates U (normalizedCoreGradient U R primalRidgeConstant x)) j
  rw [Real.norm_eq_abs] at h1
  have h2 := frameCoordinates_norm_bound U (normalizedCoreGradient U R primalRidgeConstant x)
  have h3 := neg_le_abs (frameCoordinates U (normalizedCoreGradient U R primalRidgeConstant x) j)
  linarith only [hproj, h1, h2, h3]

theorem normalizedCoreGradient_large_barrier {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (x : Euclid dx) (hx : (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) / 2 < ‖x‖) :
    primalBarrierConstant / 2 ≤ ‖normalizedCoreGradient U (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) primalRidgeConstant x‖ := by
  let R := primalRadiusConstant * Real.sqrt (n + 1 : ℝ)
  let g := gradient coreChain (compressedCoordinates U 1 R x)
  have h1 : ‖radialCompressionDerivative R x (U g)‖ ≤ 10 ^ 6 * Real.sqrt (n + 1 : ℝ) := by
    exact (radialCompressionDerivative_norm_apply x (U g)).trans
      (by simpa only [U.norm_map] using coreChain_gradient_original_bound (compressedCoordinates U 1 R x))
  have h2 : ‖primalRidgeConstant • x‖ ≤
      ‖radialCompressionDerivative R x (U g) + primalRidgeConstant • x‖ + ‖radialCompressionDerivative R x (U g)‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le
      (radialCompressionDerivative R x (U g) + primalRidgeConstant • x) (radialCompressionDerivative R x (U g))
  have h3 := mul_lt_mul_of_pos_left hx primalRidgeConstant_pos
  have he : primalRidgeConstant * (primalRadiusConstant * Real.sqrt (n + 1 : ℝ) / 2) =
      5000000 * Real.sqrt (n + 1 : ℝ) := by
    unfold primalRidgeConstant primalRadiusConstant
    field_simp [primalBarrierConstant_pos.ne']
    ring
  rw [he] at h3
  have hs : 1 ≤ Real.sqrt (n + 1 : ℝ) := Real.one_le_sqrt.mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos primalRidgeConstant_pos] at h2
  change _ ≤ ‖radialCompressionDerivative R x (U g) + primalRidgeConstant • x‖
  nlinarith only [h1, h2, h3, hs, primalBarrierConstant_le_one]

theorem normalizedCoreGradient_barrier {n dx : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
    (x : Euclid dx)
    (hlast : |compressedCoordinates U 1 (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) x (Fin.last n)| ≤ 1 / 4) :
    primalBarrierConstant / 2 ≤ ‖normalizedCoreGradient U (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) primalRidgeConstant x‖ := by
  by_cases hx : ‖x‖ ≤ (primalRadiusConstant * Real.sqrt (n + 1 : ℝ)) / 2
  · exact normalizedCoreGradient_small_barrier U x hx hlast
  · exact normalizedCoreGradient_large_barrier U x (lt_of_not_ge hx)

end FreshGradientMinimax
