import FreshGradientMinimax.FramedAcceleratedCap

/-! Ambient cap weight control, retaining the full ambient radial wall. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
def framedAcceleratedGapGradientY (δ : ℝ) (u : Euclid (k * 2 + 1))
    (y : Euclid dy) : Euclid dy :=
  (40 : ℝ) • y - framedRobinGradientY V δ u y

theorem framedAcceleratedGap_hasFDerivAt_y {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (fun z => ambientAcceleratedWall n k z - framedRobinEnergy V δ u z)
      (innerSL ℝ (framedAcceleratedGapGradientY V δ u y)) y := by
  simpa only [← map_sub, framedAcceleratedGapGradientY] using
    (ambientAcceleratedWall_hasFDerivAt n k y).sub (framedRobinEnergy_hasFDerivAt_y V hδ u y)

theorem framedAcceleratedGapGradientY_norm_on_ball (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : ‖y‖ ≤ 2 * acceleratedDualRadius n k) :
    ‖framedAcceleratedGapGradientY V δ u y‖ ≤ 100 * acceleratedDualRadius n k := by
  have h := norm_sub_le ((40 : ℝ) • y) (framedRobinGradientY V δ u y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 40)] at h
  change ‖framedAcceleratedGapGradientY V δ u y‖ ≤ _ at h
  linarith only [h, framedRobinGradientY_norm_input V hn hδ u y, hy,
    acceleratedDualRadius_sqrt_bound n k, Real.sqrt_nonneg (k + 1 : ℕ)]

theorem framedAcceleratedCapWeight_exterior (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    framedAcceleratedCapWeight V δ u y = 1 := by
  have hR := acceleratedDualRadius_pos n k
  have hs := pow_le_pow_left₀ (show 0 ≤ 2 * acceleratedDualRadius n k by positivity) hy 2
  have hQ := (framedRobinEnergy_bounds V hn hδ u y).2
  have hr := acceleratedDualRadius_growth n k
  have hgap : acceleratedDualRadius n k ^ 2 ≤ ambientAcceleratedWall n k y - framedRobinEnergy V δ u y := by
    unfold ambientAcceleratedWall
    nlinarith only [hs, hQ, hr, sq_nonneg (acceleratedDualRadius n k)]
  unfold framedAcceleratedCapWeight
  rw [smoothRampSlope_clamp (sq_pos_of_pos hR)]
  exact min_eq_left (((one_le_div (sq_pos_of_pos hR)).mpr hgap).trans (le_max_right _ _))

theorem framedAcceleratedCapWeight_difference_u (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid dy) :
    |framedAcceleratedCapWeight V δ u y - framedAcceleratedCapWeight V δ v y| ≤
      (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) * ‖u - v‖ := by
  apply smoothRampSlope_comp_bound (sq_pos_of_pos (acceleratedDualRadius_pos n k))
  have h := scalar_gradient_bound_global (fun w => framedRobinEnergy_hasFDerivAt_u V hδ w y)
    (fun w => framedRobinGradientU_norm_radius V hn hδ w y) u v
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using h

theorem framedAcceleratedCapWeight_difference_y (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid dy) :
    |framedAcceleratedCapWeight V δ u y - framedAcceleratedCapWeight V δ u z| ≤
      (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) * ‖y - z‖ := by
  have hR := acceleratedDualRadius_pos n k
  apply ball_bound_constant_outside (by positivity : 0 ≤ 100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2)
    (1 : ℝ) (R := 2 * acceleratedDualRadius n k)
  · intro a b ha hb
    rw [Real.norm_eq_abs]
    exact smoothRampSlope_comp_bound (sq_pos_of_pos hR)
      (scalar_gradient_bound_on_ball (framedAcceleratedGap_hasFDerivAt_y V hδ u)
        (framedAcceleratedGapGradientY_norm_on_ball V hn hδ u) ha hb)
  · exact framedAcceleratedCapWeight_exterior V hn hδ u

end FreshGradientMinimax
