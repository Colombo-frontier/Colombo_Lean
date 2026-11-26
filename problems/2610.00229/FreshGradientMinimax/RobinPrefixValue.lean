import FreshGradientMinimax.AcceleratedPrefixCoordinates
import FreshGradientMinimax.RobinBlockEdgeCoordinates

/-! The actual flat-Huber energy is unchanged by the next-stage prefix
under the relaxed hiding event. Every row is checked explicitly. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem robinMultiEnergy_prefix_value {n k t : ℕ} (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2)))
    (hu : ∀ j, t < acceleratedPrimalStage n j → |u j| ≤ 2 * acceleratedHidingThreshold n k)
    (hy : ∀ j, t < acceleratedDualStage n j → |y j| ≤ 2 * acceleratedHidingThreshold n k) :
    robinMultiEnergy n k (acceleratedThreshold n k) u y =
      robinMultiEnergy n k (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) u) (acceleratedDualPrefix n k (t + 1) y) := by
  have hp := acceleratedPrimalPrefix_local_pair u hu
  have hd := acceleratedDualPrefix_local_pair y hy
  have hc := robin_edge_coefficient_bounds n
  unfold robinMultiEnergy boundedEnergy
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective e
  refine Fin.lastCases ?_ (fun a => ?_) a
  · simp only [robinBlockEdges_last, clipVector_apply]
    exact accelerated_adjacent_boundedEdge_agreement n hk (acceleratedStages_last_edge n i).symm
      (by simpa only [abs_neg] using hc.1) (by simpa only [abs_neg] using hc.2.2.1)
      (hd _) (hp _).clip
  · refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.castSucc_zero, robinBlockEdges_first, clipVector_apply]
      exact accelerated_adjacent_boundedEdge_agreement n hk (acceleratedStages_first_edge n i)
        (by simpa only [abs_neg] using hc.2.1) hc.1 (hp _).clip (hd _)
    · simp only [robinBlockEdges_interior]
      exact accelerated_adjacent_boundedEdge_agreement n hk (acceleratedStages_internal_edge n i a)
        (by simpa only [abs_neg] using hc.2.2.2) hc.2.2.2 (hd _) (hd _)

end FreshGradientMinimax
