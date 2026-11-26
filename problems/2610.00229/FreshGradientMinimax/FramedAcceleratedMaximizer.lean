import FreshGradientMinimax.FramedAcceleratedCap

/-! Actual global maximizers in arbitrary ambient space. Projection
contraction proves the upper bound; the lifted intrinsic point attains it. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n k dy : ℕ} (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

def framedAcceleratedUncapped (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) : ℝ :=
  acceleratedPrimal n k δ u - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 - framedRobinEnergy V δ u y

def framedAcceleratedMaximizer (δ : ℝ) (u : Euclid (k * 2 + 1)) (hδ : 0 ≤ δ) : Euclid dy :=
  V (acceleratedHuberMaximizer n k δ u hδ)

theorem framedAcceleratedUncapped_le_projected (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedAcceleratedUncapped V δ u y ≤ acceleratedUncapped n k δ u (frameCoordinates V y) := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) (frameCoordinates_norm_bound V y) 2
  unfold framedAcceleratedUncapped acceleratedUncapped framedRobinEnergy
  exact sub_le_sub_right (sub_le_sub_left
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ robinStep (n + 2) ^ 2 / 2)) _) _

theorem framedAcceleratedUncapped_frame (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    framedAcceleratedUncapped V δ u (V y) = acceleratedUncapped n k δ u y := by
  simp only [framedAcceleratedUncapped, acceleratedUncapped, framedRobinEnergy, V.norm_map, frameCoordinates_frame]

theorem framedAcceleratedCap_frame (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    framedAcceleratedCap V δ u (V y) = acceleratedCap n k δ u y := by
  simp only [framedAcceleratedCap, acceleratedCap, framedRobinEnergy, ambientAcceleratedWall, acceleratedWall,
    V.norm_map, frameCoordinates_frame]

theorem framedAcceleratedMaximizer_max {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    framedAcceleratedUncapped V δ u y ≤ framedAcceleratedUncapped V δ u (framedAcceleratedMaximizer V δ u hδ) := by
  rw [framedAcceleratedMaximizer, framedAcceleratedUncapped_frame]
  exact (framedAcceleratedUncapped_le_projected V δ u y).trans
    (acceleratedHuberMaximizer_max n k hδ u (frameCoordinates V y))

theorem framedAcceleratedMaximizer_norm (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    ‖framedAcceleratedMaximizer V (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le‖ ≤
      43 * (n + 2 : ℕ) * Real.sqrt (k + 1 : ℕ) := by
  rw [framedAcceleratedMaximizer, V.norm_map]
  exact acceleratedHuberMaximizer_threshold_norm hn hk u

theorem framedAcceleratedMaximizer_in_core (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    ‖framedAcceleratedMaximizer V (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le‖ <
      acceleratedDualRadius n k / 2 := by
  rw [framedAcceleratedMaximizer, V.norm_map]
  exact acceleratedHuberMaximizer_in_core hn hk u

end FreshGradientMinimax
