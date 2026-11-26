import FreshGradientMinimax.AcceleratedStageMasks
import FreshGradientMinimax.AcceleratedHidingMargin

/-! Coordinate certificates for a prefix that reveals one additional
vertex. They certify both exposed equality and small hidden values. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def StageLocalPair (t s : ℕ) (τ a b : ℝ) : Prop :=
  (s ≤ t + 1 → a = b) ∧ (t < s → |a| ≤ 2 * τ ∧ |b| ≤ 2 * τ)

theorem stageMask_local_pair {m : ℕ} (stage : Fin m → ℕ) (t : ℕ) {τ : ℝ}
    (u : Euclid m) (j : Fin m) (hu : t < stage j → |u j| ≤ 2 * τ) :
    StageLocalPair t (stage j) τ (u j) (stageMask stage (t + 1) u j) := by
  constructor
  · intro hj
    exact (stageMask_known stage (t + 1) u j hj).symm
  · intro hj
    exact ⟨hu hj, (stageMask_abs_le stage (t + 1) u j).trans (hu hj)⟩

theorem StageLocalPair.clip {t s : ℕ} {τ a b : ℝ} (h : StageLocalPair t s τ a b) :
    StageLocalPair t s τ (smoothClip 2 a) (smoothClip 2 b) := by
  constructor
  · intro hs
    rw [h.1 hs]
  · intro hs
    exact ⟨(smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) a).trans (h.2 hs).1,
      (smoothClip_le_abs (by norm_num : (0 : ℝ) < 2) b).trans (h.2 hs).2⟩

theorem accelerated_adjacent_boundedEdge_agreement (n : ℕ) {k t s r : ℕ} (hk : 0 < k)
    (hsr : r = s + 1) {a b u v U V : ℝ}
    (ha : |a| ≤ 1 + Real.sqrt (robinC (n + 2))) (hb : |b| ≤ 1 + Real.sqrt (robinC (n + 2)))
    (hu : StageLocalPair t s (acceleratedHidingThreshold n k) u U)
    (hv : StageLocalPair t r (acceleratedHidingThreshold n k) v V) :
    boundedFlatEdge (acceleratedThreshold n k) 1000 (a * u + b * v) =
      boundedFlatEdge (acceleratedThreshold n k) 1000 (a * U + b * V) := by
  by_cases hr : r ≤ t + 1
  · rw [hu.1 (by omega), hv.1 hr]
  · have hs : t < s := by omega
    have hr' : t < r := by omega
    rw [boundedFlatEdge_flat (acceleratedThreshold_pos n hk).le (by norm_num)
      (accelerated_small_linear_edge_margin n hk ha hb (hu.2 hs).1 (hv.2 hr').1),
      boundedFlatEdge_flat (acceleratedThreshold_pos n hk).le (by norm_num)
      (accelerated_small_linear_edge_margin n hk ha hb (hu.2 hs).2 (hv.2 hr').2)]

theorem acceleratedPrimalPrefix_local_pair {n k t : ℕ} (u : Euclid (k * 2 + 1))
    (hu : ∀ j, t < acceleratedPrimalStage n j → |u j| ≤ 2 * acceleratedHidingThreshold n k)
    (j : Fin (k * 2 + 1)) :
    StageLocalPair t (acceleratedPrimalStage n j) (acceleratedHidingThreshold n k)
      (u j) (acceleratedPrimalPrefix n k (t + 1) u j) :=
  stageMask_local_pair _ _ _ _ (hu j)

theorem acceleratedDualPrefix_local_pair {n k t : ℕ} (y : Euclid (k * (n + 2)))
    (hy : ∀ j, t < acceleratedDualStage n j → |y j| ≤ 2 * acceleratedHidingThreshold n k)
    (j : Fin (k * (n + 2))) :
    StageLocalPair t (acceleratedDualStage n j) (acceleratedHidingThreshold n k)
      (y j) (acceleratedDualPrefix n k (t + 1) y j) :=
  stageMask_local_pair _ _ _ _ (hy j)

end FreshGradientMinimax
