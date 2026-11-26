import FreshGradientMinimax.RobinPrefixValue
import FreshGradientMinimax.AcceleratedPrimalPrefixValue

/-! Strict threshold margins upgrade value locality to equality on a
neighborhood. This works for arbitrary continuous coordinate readings. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Filter Topology

theorem stage_hidden_eventually {E : Type*} [TopologicalSpace E] {m : ℕ}
    (stage : Fin m → ℕ) (t : ℕ) {τ : ℝ} (hτ : 0 < τ) {A : E → Euclid m} {x : E}
    (hA : ContinuousAt A x) (hx : ∀ j, t < stage j → |A x j| ≤ τ) :
    ∀ᶠ v in 𝓝 x, ∀ j, t < stage j → |A v j| ≤ 2 * τ := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : t < stage j
  · have hc : ContinuousAt (fun v => |A v j|) x :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt.comp hA).abs
    have hlt : |A x j| < 2 * τ := by linarith only [hx j hj, hτ]
    exact (hc.eventually (gt_mem_nhds hlt)).mono (fun v hv _ => hv.le)
  · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)

theorem acceleratedPrimal_prefix_eventuallyEq {E : Type*} [TopologicalSpace E]
    {n k t : ℕ} (hk : 0 < k) {A : E → Euclid (k * 2 + 1)} {x : E}
    (hA : ContinuousAt A x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k) :
    (fun v => acceleratedPrimal n k (acceleratedThreshold n k) (A v)) =ᶠ[𝓝 x]
      (fun v => acceleratedPrimal n k (acceleratedThreshold n k) (acceleratedPrimalPrefix n k (t + 1) (A v))) := by
  filter_upwards [stage_hidden_eventually (acceleratedPrimalStage n) t
    (acceleratedHidingThreshold_pos n hk) hA hx] with v hv
  exact acceleratedPrimal_prefix_value hk (A v) hv

theorem robinMultiEnergy_prefix_eventuallyEq {E : Type*} [TopologicalSpace E]
    {n k t : ℕ} (hk : 0 < k) {A : E → Euclid (k * 2 + 1)} {B : E → Euclid (k * (n + 2))} {x : E}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k)
    (hy : ∀ j, t < acceleratedDualStage n j → |B x j| ≤ acceleratedHidingThreshold n k) :
    (fun v => robinMultiEnergy n k (acceleratedThreshold n k) (A v) (B v)) =ᶠ[𝓝 x]
      (fun v => robinMultiEnergy n k (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v)) (acceleratedDualPrefix n k (t + 1) (B v))) := by
  filter_upwards [stage_hidden_eventually (acceleratedPrimalStage n) t
    (acceleratedHidingThreshold_pos n hk) hA hx,
    stage_hidden_eventually (acceleratedDualStage n) t (acceleratedHidingThreshold_pos n hk) hB hy] with v hu hv
  exact robinMultiEnergy_prefix_value hk (A v) (B v) hu hv

theorem acceleratedPrimal_prefix_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k t : ℕ} (hk : 0 < k) {A : E → Euclid (k * 2 + 1)} {x : E}
    (hA : ContinuousAt A x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k) :
    fderiv ℝ (fun v => acceleratedPrimal n k (acceleratedThreshold n k) (A v)) x =
      fderiv ℝ (fun v => acceleratedPrimal n k (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v))) x :=
  (acceleratedPrimal_prefix_eventuallyEq hk hA hx).fderiv_eq

theorem robinMultiEnergy_prefix_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k t : ℕ} (hk : 0 < k) {A : E → Euclid (k * 2 + 1)} {B : E → Euclid (k * (n + 2))} {x : E}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x)
    (hx : ∀ j, t < acceleratedPrimalStage n j → |A x j| ≤ acceleratedHidingThreshold n k)
    (hy : ∀ j, t < acceleratedDualStage n j → |B x j| ≤ acceleratedHidingThreshold n k) :
    fderiv ℝ (fun v => robinMultiEnergy n k (acceleratedThreshold n k) (A v) (B v)) x =
      fderiv ℝ (fun v => robinMultiEnergy n k (acceleratedThreshold n k)
        (acceleratedPrimalPrefix n k (t + 1) (A v)) (acceleratedDualPrefix n k (t + 1) (B v))) x :=
  (robinMultiEnergy_prefix_eventuallyEq hk hA hB hx hy).fderiv_eq

end FreshGradientMinimax
