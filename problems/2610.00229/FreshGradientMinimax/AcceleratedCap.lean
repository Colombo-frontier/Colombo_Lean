import FreshGradientMinimax.AcceleratedMaximizerBounds
import FreshGradientMinimax.RadialCap

/-! The original E.2 radial cap, including its exact core and exterior regions. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedWall (n k : ℕ) (y : Euclid (k * (n + 2))) : ℝ :=
  20 * (‖y‖ ^ 2 - acceleratedDualRadius n k ^ 2)

def acceleratedCap (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : ℝ :=
  smoothMaximum (acceleratedDualRadius n k ^ 2) (robinMultiEnergy n k δ u y) (acceleratedWall n k y)

def acceleratedCapWeight (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : ℝ :=
  smoothRampSlope (acceleratedDualRadius n k ^ 2) (acceleratedWall n k y - robinMultiEnergy n k δ u y)

def acceleratedCapGradientY (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 2)) :=
  (1 - acceleratedCapWeight n k δ u y) • robinMultiGradientY n k δ u y +
    acceleratedCapWeight n k δ u y • ((40 : ℝ) • y)

theorem acceleratedDualRadius_sq (n k : ℕ) :
    acceleratedDualRadius n k ^ 2 = 10 ^ 6 * (n + 2 : ℕ) ^ 2 * (k + 1 : ℕ) := by
  unfold acceleratedDualRadius
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

theorem acceleratedDualRadius_growth (n k : ℕ) :
    2000 * (k + 1 : ℕ) ≤ acceleratedDualRadius n k ^ 2 := by
  have hN : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hN2 : (1 : ℝ) ≤ (n + 2 : ℕ) ^ 2 := by nlinarith only [hN]
  have h := mul_le_mul_of_nonneg_right hN2 (Nat.cast_nonneg (α := ℝ) (k + 1))
  rw [acceleratedDualRadius_sq]
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) (k + 1)]

theorem acceleratedCap_ge_energy (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    robinMultiEnergy n k δ u y ≤ acceleratedCap n k δ u y :=
  smoothMaximum_ge_left (sq_pos_of_pos (acceleratedDualRadius_pos n k)) _ _

theorem acceleratedCap_core {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) {y : Euclid (k * (n + 2))} (hy : ‖y‖ ≤ acceleratedDualRadius n k) :
    acceleratedCap n k δ u y = robinMultiEnergy n k δ u y := by
  apply smoothMaximum_left
  have hs := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hQ := (robinMultiEnergy_bounds hn hδ u y).1
  unfold acceleratedWall
  linarith only [hs, hQ]

theorem acceleratedCap_exterior {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) {y : Euclid (k * (n + 2))} (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    acceleratedCap n k δ u y = acceleratedWall n k y - acceleratedDualRadius n k ^ 2 / 2 := by
  apply smoothMaximum_right (sq_pos_of_pos (acceleratedDualRadius_pos n k))
  have hs := pow_le_pow_left₀ (show 0 ≤ 2 * acceleratedDualRadius n k by have := acceleratedDualRadius_pos n k; positivity) hy 2
  have hQ := (robinMultiEnergy_bounds hn hδ u y).2
  have hR := acceleratedDualRadius_growth n k
  unfold acceleratedWall
  nlinarith only [hs, hQ, hR, sq_nonneg (acceleratedDualRadius n k)]

theorem acceleratedWall_hasFDerivAt (n k : ℕ) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (acceleratedWall n k) (innerSL ℝ ((40 : ℝ) • y)) y := by
  convert radialWall_hasFDerivAt 5 (acceleratedDualRadius n k) y using 1
  · funext z
    unfold acceleratedWall radialWall
    ring
  · norm_num

theorem acceleratedWall_convex (n k : ℕ) : ConvexOn ℝ Set.univ (acceleratedWall n k) := by
  convert (radialWall_convex (E := Euclid (k * (n + 2)))
    (by norm_num : (0 : ℝ) ≤ 5) (acceleratedDualRadius n k)) using 1
  funext z
  unfold acceleratedWall radialWall
  ring

theorem acceleratedCap_convex_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    ConvexOn ℝ Set.univ (acceleratedCap n k δ u) :=
  smoothMaximum_comp_convex (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (robinMultiEnergy_convex_y n k hδ u) (acceleratedWall_convex n k)

theorem acceleratedCap_hasFDerivAt_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (acceleratedCap n k δ u) (innerSL ℝ (acceleratedCapGradientY n k δ u y)) y := by
  have h := smoothMaximum_comp_hasFDerivAt (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (robinMultiEnergy_hasFDerivAt_y n k hδ u y) (acceleratedWall_hasFDerivAt n k y)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedCapGradientY, acceleratedCapWeight, innerSL_apply, inner_add_left, real_inner_smul_left]

theorem acceleratedCap_joint_contDiff (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid (k * (n + 2)) => acceleratedCap n k δ z.1 z.2) := by
  have hW : ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid (k * (n + 2)) => acceleratedWall n k z.2) :=
    contDiff_const.mul (((contDiff_norm_sq ℝ).comp contDiff_snd).sub contDiff_const)
  exact (smoothMaximum_contDiff (sq_pos_of_pos (acceleratedDualRadius_pos n k))).comp
    ((robinMultiEnergy_joint_contDiff n k hδ).prodMk hW)

end FreshGradientMinimax
