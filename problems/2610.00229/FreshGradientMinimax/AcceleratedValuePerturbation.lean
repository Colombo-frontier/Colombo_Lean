import FreshGradientMinimax.AcceleratedUncappedModel
import FreshGradientMinimax.AcceleratedThresholdGradient
import FreshGradientMinimax.AcceleratedMaximizerBounds

/-! The original quantitative comparison of the true value gradients.
The proof combines Danskin's formula with actual maximizer stability. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem acceleratedValue_gradient_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (acceleratedValue n k δ) u - gradient acceleratedIdealValue u‖ ≤
      200 * (n + 2 : ℕ) ^ 2 * δ * Real.sqrt (k * (n + 3) : ℕ) := by
  rw [acceleratedValue_gradient hn hδ, acceleratedIdealValue_gradient hn]
  let yd := acceleratedHuberMaximizer n k δ u hδ
  let y0 := acceleratedQuadraticMaximizer n k u
  have h := norm_sub_triangle (acceleratedUncappedGradientU n k δ u yd)
    (acceleratedUncappedGradientU n k δ u y0) (acceleratedUncappedGradientU n k 0 u y0)
  have hm := acceleratedUncappedGradientU_difference_y hn hδ u yd y0
  have hp := acceleratedUncappedGradientU_perturbation hn hδ u y0
  have hd := acceleratedHuberMaximizer_displacement hn hδ u
  change ‖yd - y0‖ ≤ _ at hd
  have hN : (1 : ℝ) ≤ (n + 2 : ℕ) ^ 2 := by
    have hn1 : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
    nlinarith only [hn1]
  have hscale := mul_le_mul_of_nonneg_right hN
    (mul_nonneg hδ (Real.sqrt_nonneg (k * (n + 3) : ℕ)))
  change ‖acceleratedUncappedGradientU n k δ u yd - acceleratedUncappedGradientU n k 0 u y0‖ ≤ _
  nlinarith only [h, hm, hp, hd, hscale,
    mul_nonneg (sq_nonneg ((n + 2 : ℕ) : ℝ)) (mul_nonneg hδ (Real.sqrt_nonneg (k * (n + 3) : ℕ)))]

theorem acceleratedValue_gradient_comparison {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (acceleratedValue n k (acceleratedThreshold n k)) u - gradient acceleratedIdealValue u‖ ≤
      primalRidgeConstant / 100 := by
  have h := acceleratedValue_gradient_perturbation hn (acceleratedThreshold_pos n hk).le u
  have hs := acceleratedThreshold_displacement_scale n hk
  nlinarith only [h, hs, primalRidgeConstant_pos]

theorem acceleratedValue_gradient_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (acceleratedValue n k δ) u‖ ≤ 15000 * Real.sqrt (k + 1 : ℕ) := by
  rw [acceleratedValue_gradient hn hδ]
  exact acceleratedUncappedGradientU_norm hn hδ u _

end FreshGradientMinimax
