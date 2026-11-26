import FreshGradientMinimax.AcceleratedRawExterior
import FreshGradientMinimax.AcceleratedPrefixNeighborhood

/-! Actual protected objectives agree locally with prefix objectives.
Large dual queries use the radial cap, so only bounded dual queries
require the dual hiding event. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Filter Topology
variable {E : Type*} [TopologicalSpace E] {n k dy t : ℕ}

theorem acceleratedRawProtected_prefix_interior
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hk : 0 < k)
    {A : E → Euclid (k * 2 + 1)} {Y : E → Euclid dy} {x : E}
    (hA : ContinuousAt A x) (hY : ContinuousAt Y x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k)
    (hy : ∀ j, t < acceleratedDualStage n j → |B (Y x) j| ≤ acceleratedHidingThreshold n k) :
    (fun v => acceleratedRawProtected B (acceleratedThreshold n k) (A v) (Y v)) =ᶠ[𝓝 x]
      (fun v => acceleratedRawProtected ((acceleratedDualPrefix n k (t + 1)).comp B) (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v)) (Y v)) := by
  filter_upwards [acceleratedPrimal_prefix_eventuallyEq hk hA hx,
    robinMultiEnergy_prefix_eventuallyEq hk hA (B.continuous.continuousAt.comp hY) hx hy] with v hD hQ
  simp only [Function.comp_def] at hQ
  simp only [acceleratedRawProtected, ContinuousLinearMap.comp_apply, hD, hQ]

theorem acceleratedRawProtected_prefix_exterior
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hB : ∀ y, ‖B y‖ ≤ ‖y‖)
    (hn : 10 ≤ n + 2) (hk : 0 < k)
    {A : E → Euclid (k * 2 + 1)} {Y : E → Euclid dy} {x : E}
    (hA : ContinuousAt A x) (hY : ContinuousAt Y x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k)
    (hy : 2 * acceleratedDualRadius n k ≤ ‖Y x‖) :
    (fun v => acceleratedRawProtected B (acceleratedThreshold n k) (A v) (Y v)) =ᶠ[𝓝 x]
      (fun v => acceleratedRawProtected ((acceleratedDualPrefix n k (t + 1)).comp B) (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v)) (Y v)) := by
  have hP : ContinuousAt (fun v => acceleratedPrimalPrefix n k (t + 1) (A v)) x :=
    (acceleratedPrimalPrefix n k (t + 1)).continuous.continuousAt.comp hA
  filter_upwards [acceleratedPrimal_prefix_eventuallyEq hk hA hx,
    acceleratedRawProtected_radial_eventuallyEq B hB hn (acceleratedThreshold_pos n hk).le hA hY hy,
    acceleratedRawProtected_radial_eventuallyEq ((acceleratedDualPrefix n k (t + 1)).comp B)
      (acceleratedDualPrefix_contraction B hB (t + 1)) hn (acceleratedThreshold_pos n hk).le hP hY hy]
    with v hD hfull hprefix
  rw [hfull, hprefix, hD]

theorem acceleratedRawProtected_prefix_eventuallyEq
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hB : ∀ y, ‖B y‖ ≤ ‖y‖)
    (hn : 10 ≤ n + 2) (hk : 0 < k)
    {A : E → Euclid (k * 2 + 1)} {Y : E → Euclid dy} {x : E}
    (hA : ContinuousAt A x) (hY : ContinuousAt Y x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k)
    (hy : ‖Y x‖ ≤ 2 * acceleratedDualRadius n k →
      ∀ j, t < acceleratedDualStage n j → |B (Y x) j| ≤ acceleratedHidingThreshold n k) :
    (fun v => acceleratedRawProtected B (acceleratedThreshold n k) (A v) (Y v)) =ᶠ[𝓝 x]
      (fun v => acceleratedRawProtected ((acceleratedDualPrefix n k (t + 1)).comp B) (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v)) (Y v)) := by
  by_cases h : ‖Y x‖ ≤ 2 * acceleratedDualRadius n k
  · exact acceleratedRawProtected_prefix_interior B hk hA hY hx (hy h)
  · exact acceleratedRawProtected_prefix_exterior B hB hn hk hA hY hx (le_of_not_ge h)

end FreshGradientMinimax
