import FreshGradientMinimax.FramedAcceleratedMaximizer
import FreshGradientMinimax.AcceleratedProtectedModel

/-! The protected E objective in arbitrary ambient dual dimension, with
the full isotropic quadratic and its true joint derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

def framedAcceleratedProtected (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  acceleratedPrimal n k δ u - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 - framedAcceleratedCap V δ u y

def framedAcceleratedGradientU (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid (k * 2 + 1) :=
  acceleratedPrimalGradient n k δ u - framedAcceleratedCapGradientU V δ u y

def framedAcceleratedGradientY (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : Euclid dy :=
  -(robinStep (n + 2) ^ 2 • y) - framedAcceleratedCapGradientY V δ u y

theorem framedAcceleratedProtected_hasFDerivAt_u {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => framedAcceleratedProtected V δ v y) (innerSL ℝ (framedAcceleratedGradientU V δ u y)) u := by
  have h := ((acceleratedPrimal_hasFDerivAt n k hδ u).sub
    (hasFDerivAt_const (robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2) u)).sub
    (framedAcceleratedCap_hasFDerivAt_u V hδ u y)
  apply h.congr_fderiv
  ext v
  simp [framedAcceleratedGradientU, innerSL_apply, inner_sub_left]

theorem framedAcceleratedProtected_hasFDerivAt_y {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    HasFDerivAt (framedAcceleratedProtected V δ u) (innerSL ℝ (framedAcceleratedGradientY V δ u y)) y := by
  have hn := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (robinStep (n + 2) ^ 2 / 2)
  have h := ((hasFDerivAt_const (acceleratedPrimal n k δ u) y).sub hn).sub
    (framedAcceleratedCap_hasFDerivAt_y V hδ u y)
  apply h.congr_fderiv
  ext v
  simp [framedAcceleratedGradientY, innerSL_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
  ring

theorem framedAcceleratedProtected_joint_contDiff {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid dy => framedAcceleratedProtected V δ z.1 z.2) :=
  (((acceleratedPrimal_contDiff n k hδ).comp contDiff_fst).sub
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))).sub (framedAcceleratedCap_joint_contDiff V hδ)

theorem framedAcceleratedProtected_hasFDerivAt_joint {δ : ℝ} (hδ : 0 ≤ δ) (z : Joint (k * 2 + 1) dy) :
    HasFDerivAt (fun w : Joint (k * 2 + 1) dy => framedAcceleratedProtected V δ w.1 w.2)
      ((innerSL ℝ (framedAcceleratedGradientU V δ z.1 z.2)).coprod
        (innerSL ℝ (framedAcceleratedGradientY V δ z.1 z.2))) z := by
  have h := joint_hasFDerivAt_gradient ((framedAcceleratedProtected_joint_contDiff V hδ).differentiable (by norm_num) z)
  have hx := (hasGradientAt_iff_hasFDerivAt.mpr (framedAcceleratedProtected_hasFDerivAt_u V hδ z.1 z.2)).gradient
  have hy := (hasGradientAt_iff_hasFDerivAt.mpr (framedAcceleratedProtected_hasFDerivAt_y V hδ z.1 z.2)).gradient
  simpa only [hx, hy] using h

theorem framedAcceleratedProtected_strongConcave {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    StrongConcaveGradient (framedAcceleratedProtected V δ u) (framedAcceleratedGradientY V δ u)
      (robinStep (n + 2) ^ 2) := by
  simpa only [framedAcceleratedProtected, framedAcceleratedGradientY, inner_zero_left, add_zero, zero_sub] using
    convex_penalty_strongConcave (framedAcceleratedCap_convex_y V hδ u)
      (framedAcceleratedCap_hasFDerivAt_y V hδ u) (robinStep (n + 2) ^ 2)
      (acceleratedPrimal n k δ u) (0 : Euclid dy)

theorem framedAcceleratedGradientU_norm (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    ‖framedAcceleratedGradientU V δ u y‖ ≤ 15000 * Real.sqrt (k + 1 : ℕ) := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u) (framedAcceleratedCapGradientU V δ u y)
  change ‖framedAcceleratedGradientU V δ u y‖ ≤ _ at h
  linarith only [h, acceleratedPrimalGradient_norm hn hδ u, framedAcceleratedCapGradientU_norm V hn hδ u y]

theorem framedAcceleratedProtected_le_uncapped (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedAcceleratedProtected V δ u y ≤ framedAcceleratedUncapped V δ u y :=
  sub_le_sub_left (framedAcceleratedCap_ge_energy V δ u y) _

theorem framedAcceleratedProtected_frame (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    framedAcceleratedProtected V δ u (V y) = acceleratedProtected n k δ u y := by
  simp only [framedAcceleratedProtected, acceleratedProtected, V.norm_map, framedAcceleratedCap_frame]

theorem framedAcceleratedProtected_origin (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    framedAcceleratedProtected V δ 0 0 = -coreTheta 0 := by
  simpa only [map_zero, acceleratedProtected_origin hn hδ] using framedAcceleratedProtected_frame V δ 0 0

theorem framedAcceleratedGradientY_origin {δ : ℝ} (hδ : 0 ≤ δ) :
    framedAcceleratedGradientY V δ 0 0 = 0 := by
  simp [framedAcceleratedGradientY, framedAcceleratedCapGradientY, framedRobinGradientY,
    robinMultiGradientY_origin n k hδ]

theorem framedAcceleratedProtected_origin_max (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) (y : Euclid dy) :
    framedAcceleratedProtected V δ 0 y ≤ -coreTheta 0 := by
  have h := framedAcceleratedProtected_strongConcave V hδ 0 0 y
  rw [framedAcceleratedGradientY_origin V hδ, inner_zero_left, add_zero, framedAcceleratedProtected_origin V hn hδ] at h
  exact h.trans (sub_le_self _ (by positivity))

end FreshGradientMinimax
