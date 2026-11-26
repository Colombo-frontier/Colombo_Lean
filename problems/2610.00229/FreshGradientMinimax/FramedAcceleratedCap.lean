import FreshGradientMinimax.FramedRobinEnergy

/-! The actual ambient radial protection. The wall uses the full ambient
norm and is independent of the orthonormal frame. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

def ambientAcceleratedWall (n k : ℕ) (y : Euclid dy) : ℝ :=
  20 * (‖y‖ ^ 2 - acceleratedDualRadius n k ^ 2)

def framedAcceleratedCap (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  smoothMaximum (acceleratedDualRadius n k ^ 2) (framedRobinEnergy V δ u y) (ambientAcceleratedWall n k y)

def framedAcceleratedCapWeight (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  smoothRampSlope (acceleratedDualRadius n k ^ 2) (ambientAcceleratedWall n k y - framedRobinEnergy V δ u y)

def framedAcceleratedCapGradientY (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid dy :=
  (1 - framedAcceleratedCapWeight V δ u y) • framedRobinGradientY V δ u y +
    framedAcceleratedCapWeight V δ u y • ((40 : ℝ) • y)

def framedAcceleratedCapGradientU (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid (k * 2 + 1) :=
  (1 - framedAcceleratedCapWeight V δ u y) • framedRobinGradientU V δ u y

theorem framedAcceleratedCapWeight_bounds (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    0 ≤ framedAcceleratedCapWeight V δ u y ∧ framedAcceleratedCapWeight V δ u y ≤ 1 :=
  smoothRampSlope_bounds (sq_pos_of_pos (acceleratedDualRadius_pos n k)) _

theorem framedAcceleratedCap_ge_energy (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedRobinEnergy V δ u y ≤ framedAcceleratedCap V δ u y :=
  smoothMaximum_ge_left (sq_pos_of_pos (acceleratedDualRadius_pos n k)) _ _

theorem framedAcceleratedCap_core (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) {y : Euclid dy} (hy : ‖y‖ ≤ acceleratedDualRadius n k) :
    framedAcceleratedCap V δ u y = framedRobinEnergy V δ u y := by
  apply smoothMaximum_left
  have hs := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hQ := (framedRobinEnergy_bounds V hn hδ u y).1
  unfold ambientAcceleratedWall
  linarith only [hs, hQ]

theorem framedAcceleratedCap_exterior (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) {y : Euclid dy} (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    framedAcceleratedCap V δ u y = ambientAcceleratedWall n k y - acceleratedDualRadius n k ^ 2 / 2 := by
  apply smoothMaximum_right (sq_pos_of_pos (acceleratedDualRadius_pos n k))
  have hs := pow_le_pow_left₀ (show 0 ≤ 2 * acceleratedDualRadius n k by have := acceleratedDualRadius_pos n k; positivity) hy 2
  have hQ := (framedRobinEnergy_bounds V hn hδ u y).2
  have hR := acceleratedDualRadius_growth n k
  unfold ambientAcceleratedWall
  nlinarith only [hs, hQ, hR, sq_nonneg (acceleratedDualRadius n k)]

theorem ambientAcceleratedWall_hasFDerivAt (n k : ℕ) (y : Euclid dy) :
    HasFDerivAt (ambientAcceleratedWall n k) (innerSL ℝ ((40 : ℝ) • y)) y := by
  convert radialWall_hasFDerivAt 5 (acceleratedDualRadius n k) y using 1
  · funext z
    unfold ambientAcceleratedWall radialWall
    ring
  · norm_num

theorem ambientAcceleratedWall_convex (n k : ℕ) : ConvexOn ℝ Set.univ (ambientAcceleratedWall (dy := dy) n k) := by
  convert (radialWall_convex (E := Euclid dy) (by norm_num : (0 : ℝ) ≤ 5) (acceleratedDualRadius n k)) using 1
  funext z
  unfold ambientAcceleratedWall radialWall
  ring

theorem framedAcceleratedCap_convex_y {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    ConvexOn ℝ Set.univ (framedAcceleratedCap V δ u) :=
  smoothMaximum_comp_convex (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (framedRobinEnergy_convex_y V hδ u) (ambientAcceleratedWall_convex n k)

theorem framedAcceleratedCap_hasFDerivAt_y {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (framedAcceleratedCap V δ u) (innerSL ℝ (framedAcceleratedCapGradientY V δ u y)) y := by
  have h := smoothMaximum_comp_hasFDerivAt (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (framedRobinEnergy_hasFDerivAt_y V hδ u y) (ambientAcceleratedWall_hasFDerivAt n k y)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [framedAcceleratedCapGradientY, framedAcceleratedCapWeight, innerSL_apply, inner_add_left, real_inner_smul_left]

theorem framedAcceleratedCap_hasFDerivAt_u {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => framedAcceleratedCap V δ v y) (innerSL ℝ (framedAcceleratedCapGradientU V δ u y)) u := by
  have h := smoothMaximum_comp_hasFDerivAt (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (framedRobinEnergy_hasFDerivAt_u V hδ u y) (hasFDerivAt_const (ambientAcceleratedWall n k y) u)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [framedAcceleratedCapGradientU, framedAcceleratedCapWeight, innerSL_apply, real_inner_smul_left]

theorem framedAcceleratedCap_joint_contDiff {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid dy => framedAcceleratedCap V δ z.1 z.2) := by
  have hW : ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid dy => ambientAcceleratedWall n k z.2) :=
    contDiff_const.mul (((contDiff_norm_sq ℝ).comp contDiff_snd).sub contDiff_const)
  exact (smoothMaximum_contDiff (sq_pos_of_pos (acceleratedDualRadius_pos n k))).comp
    ((framedRobinEnergy_joint_contDiff V hδ).prodMk hW)

theorem framedAcceleratedCapGradientU_norm (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedCapGradientU V δ u y‖ ≤ 14000 * Real.sqrt (k + 1 : ℕ) := by
  have hw := framedAcceleratedCapWeight_bounds V δ u y
  unfold framedAcceleratedCapGradientU
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - framedAcceleratedCapWeight V δ u y)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (framedRobinGradientU_norm V hn hδ u y)

end FreshGradientMinimax
