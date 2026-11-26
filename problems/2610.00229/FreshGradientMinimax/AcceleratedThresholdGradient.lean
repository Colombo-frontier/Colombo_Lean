import FreshGradientMinimax.AcceleratedUncappedGradient

/-! Uniform threshold perturbation of the actual primal partial gradient.
The estimate is valid at every dual point, before choosing a maximizer. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem robinMultiPullback_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiPullback n k δ u y - robinMultiPullback n k 0 u y‖ ≤
      10 * δ * Real.sqrt (k * (n + 3) : ℕ) := by
  have h := ((robinPrimalMap n k)†).le_opNorm
    (robinMultiSlope n k δ u y - robinMultiSlope n k 0 u y)
  rw [ContinuousLinearMap.adjoint.norm_map, map_sub] at h
  change ‖robinMultiPullback n k δ u y - robinMultiPullback n k 0 u y‖ ≤ _ at h
  have hs := boundedSlope_perturbation hδ (by norm_num : (0 : ℝ) ≤ 1000)
    (robinBlockEdges n k (clipVector 2 u) y)
  have hA : ‖robinPrimalMap n k‖ ≤ 10 := (robinPrimalMap_opNorm_bound hn k).trans (by norm_num)
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul hA hs (norm_nonneg _) (by norm_num))

theorem robinMultiGradientU_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientU n k δ u y - robinMultiGradientU n k 0 u y‖ ≤
      10 * δ * Real.sqrt (k * (n + 3) : ℕ) :=
  (weightedClipGradient_sub_weights 2 (robinMultiPullback n k δ u y) (robinMultiPullback n k 0 u y) u).trans
    (robinMultiPullback_perturbation hn hδ u y)

theorem acceleratedPrimalGradient_edge_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k 0 u‖ ≤
      84 * δ * Real.sqrt (k * (n + 3) : ℕ) := by
  have hM : k * 2 ≤ k * (n + 3) := Nat.mul_le_mul_left k (by omega)
  exact (acceleratedPrimalGradient_perturbation hn hδ u).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hM)) (by positivity))

theorem acceleratedUncappedGradientU_perturbation {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedUncappedGradientU n k δ u y - acceleratedUncappedGradientU n k 0 u y‖ ≤
      94 * δ * Real.sqrt (k * (n + 3) : ℕ) := by
  have he : acceleratedUncappedGradientU n k δ u y - acceleratedUncappedGradientU n k 0 u y =
      (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k 0 u) -
        (robinMultiGradientU n k δ u y - robinMultiGradientU n k 0 u y) := by
    unfold acceleratedUncappedGradientU
    abel
  rw [he]
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u - acceleratedPrimalGradient n k 0 u)
    (robinMultiGradientU n k δ u y - robinMultiGradientU n k 0 u y)
  linarith only [h, acceleratedPrimalGradient_edge_perturbation hn hδ u,
    robinMultiGradientU_perturbation hn hδ u y]

end FreshGradientMinimax
