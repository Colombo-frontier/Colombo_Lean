import FreshGradientMinimax.AcceleratedPrefixCoordinates

/-! The original D_delta has exactly the same value after the next-stage
prefix. The seed is retained and each omitted link has a flat gate. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem accelerated_stage_flatEdge_agreement (n : ℕ) {k t s : ℕ} (hk : 0 < k) {u U : ℝ}
    (hu : StageLocalPair t s (acceleratedHidingThreshold n k) u U) :
    flatEdge (acceleratedThreshold n k) (smoothClip 2 u) =
      flatEdge (acceleratedThreshold n k) (smoothClip 2 U) := by
  by_cases hs : s ≤ t + 1
  · rw [hu.1 hs]
  · have ht : t < s := by omega
    rw [accelerated_hidden_primal_flat_margin n hk (hu.2 ht).1,
      accelerated_hidden_primal_flat_margin n hk (hu.2 ht).2]

theorem accelerated_adjacent_nonlinear_agreement (n : ℕ) {k t s r : ℕ} (hk : 0 < k)
    (hsr : r = s + 1) {u v U V : ℝ}
    (hu : StageLocalPair t s (acceleratedHidingThreshold n k) u U)
    (hv : StageLocalPair t r (acceleratedHidingThreshold n k) v V) :
    coreLinkTerm (smoothClip 2 u) (smoothClip 2 v) =
      coreLinkTerm (smoothClip 2 U) (smoothClip 2 V) := by
  by_cases hr : r ≤ t + 1
  · rw [hu.1 (by omega), hv.1 hr]
  · have ht : t < s := by omega
    rw [accelerated_hidden_nonlinear_flat_margin n hk (hu.2 ht).1,
      accelerated_hidden_nonlinear_flat_margin n hk (hu.2 ht).2]

theorem acceleratedNonlinear_prefix_value {n k t : ℕ} (hk : 0 < k)
    (u : Euclid (k * 2 + 1))
    (hu : ∀ j, t < acceleratedPrimalStage n j → |u j| ≤ 2 * acceleratedHidingThreshold n k) :
    acceleratedNonlinear (clipVector 2 u) =
      acceleratedNonlinear (clipVector 2 (acceleratedPrimalPrefix n k (t + 1) u)) := by
  unfold acceleratedNonlinear
  simp only [clipVector_apply, acceleratedPrimalPrefix_seed]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact accelerated_adjacent_nonlinear_agreement n hk (acceleratedStages_nonlinear_edge n i)
    (acceleratedPrimalPrefix_local_pair u hu _) (acceleratedPrimalPrefix_local_pair u hu _)

theorem acceleratedPrimal_prefix_value {n k t : ℕ} (hk : 0 < k)
    (u : Euclid (k * 2 + 1))
    (hu : ∀ j, t < acceleratedPrimalStage n j → |u j| ≤ 2 * acceleratedHidingThreshold n k) :
    acceleratedPrimal n k (acceleratedThreshold n k) u =
      acceleratedPrimal n k (acceleratedThreshold n k) (acceleratedPrimalPrefix n k (t + 1) u) := by
  unfold acceleratedPrimal
  rw [acceleratedNonlinear_prefix_value hk u hu]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [clipVector_apply]
  rw [accelerated_stage_flatEdge_agreement n hk (acceleratedPrimalPrefix_local_pair u hu (interleavedX i)),
    accelerated_stage_flatEdge_agreement n hk (acceleratedPrimalPrefix_local_pair u hu (interleavedZ i))]

end FreshGradientMinimax
