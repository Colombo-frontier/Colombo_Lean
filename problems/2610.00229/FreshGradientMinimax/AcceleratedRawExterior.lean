import FreshGradientMinimax.AcceleratedRawModel

/-! The raw protected cap is locally radial for large ambient dual
queries whenever the coordinate reading is a contraction. This applies
to every prefix of a genuine frame, without hiding assumptions on y. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Filter Topology
variable {n k dy : ℕ}

theorem acceleratedRawEnergy_bound (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    (hB : ∀ y, ‖B y‖ ≤ ‖y‖) (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) :
    robinMultiEnergy n k δ u (B y) ≤ 2000 * (k + 1 : ℕ) + 5 * ‖y‖ ^ 2 := by
  have h := (robinMultiEnergy_bounds hn hδ u (B y)).2
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hB y) 2
  linarith only [h, hs]

theorem acceleratedRawCap_exterior_gap (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    (hB : ∀ y, ‖B y‖ ≤ ‖y‖) (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid dy) (hy : 2 * acceleratedDualRadius n k ≤ ‖y‖) :
    acceleratedDualRadius n k ^ 2 < ambientAcceleratedWall n k y - robinMultiEnergy n k δ u (B y) := by
  have hQ := acceleratedRawEnergy_bound B hB hn hδ u y
  have hR := acceleratedDualRadius_pos n k
  have hs := pow_le_pow_left₀ (show 0 ≤ 2 * acceleratedDualRadius n k by positivity) hy 2
  have hr := acceleratedDualRadius_growth n k
  unfold ambientAcceleratedWall
  nlinarith only [hQ, hs, hr, sq_pos_of_pos hR]

theorem acceleratedRawProtected_radial_eventuallyEq {E : Type*} [TopologicalSpace E]
    (B : Euclid dy →L[ℝ] Euclid (k * (n + 2))) (hB : ∀ y, ‖B y‖ ≤ ‖y‖)
    (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    {A : E → Euclid (k * 2 + 1)} {Y : E → Euclid dy} {x : E}
    (hA : ContinuousAt A x) (hY : ContinuousAt Y x) (hy : 2 * acceleratedDualRadius n k ≤ ‖Y x‖) :
    (fun v => acceleratedRawProtected B δ (A v) (Y v)) =ᶠ[𝓝 x]
      (fun v => acceleratedPrimal n k δ (A v) - robinStep (n + 2) ^ 2 / 2 * ‖Y v‖ ^ 2 -
        (ambientAcceleratedWall n k (Y v) - acceleratedDualRadius n k ^ 2 / 2)) := by
  have hBY : ContinuousAt (fun v => B (Y v)) x := B.continuous.continuousAt.comp hY
  have hAB : ContinuousAt (fun v => (A v, B (Y v))) x := hA.prodMk hBY
  have hQ : ContinuousAt (fun v => robinMultiEnergy n k δ (A v) (B (Y v))) x :=
    ContinuousAt.comp (f := fun v : E => (A v, B (Y v)))
      (g := fun p : Joint (k * 2 + 1) (k * (n + 2)) => robinMultiEnergy n k δ p.1 p.2)
      (robinMultiEnergy_joint_contDiff n k hδ).continuous.continuousAt hAB
  have hW : ContinuousAt (fun v => ambientAcceleratedWall n k (Y v)) x :=
    continuousAt_const.mul ((hY.norm.pow 2).sub continuousAt_const)
  have hgap := (hW.sub hQ).eventually (lt_mem_nhds (acceleratedRawCap_exterior_gap B hB hn hδ (A x) (Y x) hy))
  filter_upwards [hgap] with v hv
  unfold acceleratedRawProtected
  rw [smoothMaximum_right (sq_pos_of_pos (acceleratedDualRadius_pos n k)) hv.le]

theorem acceleratedDualPrefix_contraction (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    (hB : ∀ y, ‖B y‖ ≤ ‖y‖) (t : ℕ) (y : Euclid dy) :
    ‖((acceleratedDualPrefix n k t).comp B) y‖ ≤ ‖y‖ :=
  (stageMask_norm (acceleratedDualStage n) t (B y)).trans (hB y)

end FreshGradientMinimax
