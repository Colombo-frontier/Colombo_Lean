import FreshGradientMinimax.AcceleratedProtectedValue
import FreshGradientMinimax.CoreWeightControl

/-! Uniform control of the original cap's blend weight. The radius cancels
from the gradient correction constants, including across both interfaces. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem acceleratedDualRadius_sqrt_bound (n k : ℕ) :
    1000 * Real.sqrt (k + 1 : ℕ) ≤ acceleratedDualRadius n k := by
  have hn : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have h := mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg (k + 1 : ℕ))
  unfold acceleratedDualRadius
  nlinarith only [h]

theorem boundedSlope_norm_input {m : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid m) :
    ‖boundedSlope δ b x‖ ≤ ‖x‖ := by
  have hz : boundedSlope δ b (0 : Euclid m) = 0 := by
    ext i
    exact boundedFlatSlope_flat hδ hb (by simpa only [PiLp.zero_apply, abs_zero] using hδ)
  have h := boundedSlope_difference hδ hb x 0
  simpa only [hz, sub_zero] using h

theorem robinMultiGradientY_norm_input {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientY n k δ u y‖ ≤ 4 * ‖y‖ + 120 * Real.sqrt (k + 1 : ℕ) := by
  have h := ((robinDualMap n k)†).le_opNorm (robinMultiSlope n k δ u y)
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  change ‖robinMultiGradientY n k δ u y‖ ≤ _ at h
  have h1 := mul_le_mul (robinDualMap_opNorm n k)
    (boundedSlope_norm_input hδ (by norm_num : (0 : ℝ) ≤ 1000) (robinBlockEdges n k (clipVector 2 u) y))
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hA : ‖robinPrimalMap n k‖ ≤ 10 := (robinPrimalMap_opNorm_bound hn k).trans (by norm_num)
  have hp := (robinPrimalMap n k).le_opNorm (clipVector 2 u)
  have hp1 := mul_le_mul hA (accelerated_clip_norm u) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 10)
  have he := norm_add_le (robinDualMap n k y) (robinPrimalMap n k (clipVector 2 u))
  change ‖robinBlockEdges n k (clipVector 2 u) y‖ ≤ _ at he
  change ‖robinDualMap n k‖ * ‖robinMultiSlope n k δ u y‖ ≤ _ at h1
  linarith only [h, h1, hp, hp1, he, robinDualMap_norm n k y]

def acceleratedGapGradientY (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2))) : Euclid (k * (n + 2)) :=
  (40 : ℝ) • y - robinMultiGradientY n k δ u y

theorem acceleratedGap_hasFDerivAt_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (fun z => acceleratedWall n k z - robinMultiEnergy n k δ u z)
      (innerSL ℝ (acceleratedGapGradientY n k δ u y)) y := by
  simpa only [← map_sub, acceleratedGapGradientY] using
    (acceleratedWall_hasFDerivAt n k y).sub (robinMultiEnergy_hasFDerivAt_y n k hδ u y)

theorem acceleratedGapGradientY_norm_on_ball {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) (hy : ‖y‖ ≤ 2 * acceleratedDualRadius n k) :
    ‖acceleratedGapGradientY n k δ u y‖ ≤ 100 * acceleratedDualRadius n k := by
  have h := norm_sub_le ((40 : ℝ) • y) (robinMultiGradientY n k δ u y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 40)] at h
  change ‖acceleratedGapGradientY n k δ u y‖ ≤ _ at h
  linarith only [h, robinMultiGradientY_norm_input hn hδ u y, hy,
    acceleratedDualRadius_sqrt_bound n k, Real.sqrt_nonneg (k + 1 : ℕ)]

theorem robinMultiGradientU_norm_radius {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientU n k δ u y‖ ≤ 14 * acceleratedDualRadius n k := by
  linarith only [robinMultiGradientU_norm hn hδ u y, acceleratedDualRadius_sqrt_bound n k]

theorem acceleratedCapWeight_exterior {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    acceleratedCapWeight n k δ u y = 1 := by
  have hR := acceleratedDualRadius_pos n k
  have hs := pow_le_pow_left₀ (show 0 ≤ 2 * acceleratedDualRadius n k by positivity) hy 2
  have hQ := (robinMultiEnergy_bounds hn hδ u y).2
  have hr := acceleratedDualRadius_growth n k
  have hgap : acceleratedDualRadius n k ^ 2 ≤ acceleratedWall n k y - robinMultiEnergy n k δ u y := by
    unfold acceleratedWall
    nlinarith only [hs, hQ, hr, sq_nonneg (acceleratedDualRadius n k)]
  unfold acceleratedCapWeight
  rw [smoothRampSlope_clamp (sq_pos_of_pos hR)]
  exact min_eq_left (((one_le_div (sq_pos_of_pos hR)).mpr hgap).trans (le_max_right _ _))

theorem acceleratedCapWeight_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    |acceleratedCapWeight n k δ u y - acceleratedCapWeight n k δ v y| ≤
      (14 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) * ‖u - v‖ := by
  apply smoothRampSlope_comp_bound (sq_pos_of_pos (acceleratedDualRadius_pos n k))
  have h := scalar_gradient_bound_global (fun w => robinMultiEnergy_hasFDerivAt_u n k hδ w y)
    (fun w => robinMultiGradientU_norm_radius hn hδ w y) u v
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using h

theorem acceleratedCapWeight_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    |acceleratedCapWeight n k δ u y - acceleratedCapWeight n k δ u z| ≤
      (100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2) * ‖y - z‖ := by
  have hR := acceleratedDualRadius_pos n k
  apply ball_bound_constant_outside (by positivity : 0 ≤ 100 * acceleratedDualRadius n k / acceleratedDualRadius n k ^ 2)
    (1 : ℝ) (R := 2 * acceleratedDualRadius n k)
  · intro a b ha hb
    rw [Real.norm_eq_abs]
    exact smoothRampSlope_comp_bound (sq_pos_of_pos hR)
      (scalar_gradient_bound_on_ball (acceleratedGap_hasFDerivAt_y n k hδ u)
        (acceleratedGapGradientY_norm_on_ball hn hδ u) ha hb)
  · exact acceleratedCapWeight_exterior hn hδ u

theorem radius_correction_identity {R : ℝ} (hR : 0 < R) (a b : ℝ) :
    (a * R / R ^ 2) * (b * R) = a * b := by
  field_simp
  ring

end FreshGradientMinimax
