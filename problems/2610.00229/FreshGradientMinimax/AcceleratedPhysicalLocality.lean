import FreshGradientMinimax.AcceleratedRawLocality

/-! The prefix reply is the actual gradient of the physical hard
instance at every good query, including unbounded dual queries. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open Filter Topology
variable {n k dx dy t : ℕ}

theorem acceleratedRawPhysical_prefix_eventuallyEq
    (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1)) (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    (hB : ∀ y, ‖B y‖ ≤ ‖y‖) (hn : 10 ≤ n + 2) (hk : 0 < k) (L ε : ℝ) (z : Joint dx dy)
    (hx : ∀ j, t < acceleratedPrimalStage n j →
      |A (radialCompression (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • z.1)) j| ≤
        acceleratedHidingThreshold n k)
    (hy : ‖(acceleratedLengthScale L ε)⁻¹ • z.2‖ ≤ 2 * acceleratedDualRadius n k →
      ∀ j, t < acceleratedDualStage n j →
        |B ((acceleratedLengthScale L ε)⁻¹ • z.2) j| ≤ acceleratedHidingThreshold n k) :
    (fun w : Joint dx dy => acceleratedRawPhysical A B L ε w.1 w.2) =ᶠ[𝓝 z]
      (fun w => acceleratedPrefixObjective A B L ε (t + 1) w.1 w.2) := by
  have hA : ContinuousAt (fun w : Joint dx dy =>
      A (radialCompression (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • w.1))) z :=
    A.continuous.continuousAt.comp
      ((radialCompression_contDiff (m := 1) _).continuous.continuousAt.comp
        (continuousAt_const.smul continuousAt_fst))
  have hY : ContinuousAt (fun w : Joint dx dy => (acceleratedLengthScale L ε)⁻¹ • w.2) z :=
    continuousAt_const.smul continuousAt_snd
  have he := acceleratedRawProtected_prefix_eventuallyEq B hB hn hk hA hY hx hy
  filter_upwards [he] with w hw
  simp only [acceleratedPrefixObjective, acceleratedRawPhysical, acceleratedRawObjective,
    ContinuousLinearMap.comp_apply]
  rw [hw]

theorem acceleratedRawPhysical_prefix_reply
    (A : Euclid dx →L[ℝ] Euclid (k * 2 + 1)) (B : Euclid dy →L[ℝ] Euclid (k * (n + 2)))
    (hB : ∀ y, ‖B y‖ ≤ ‖y‖) (hn : 10 ≤ n + 2) (hk : 0 < k) (L ε : ℝ) (z : Joint dx dy)
    (hx : ∀ j, t < acceleratedPrimalStage n j →
      |A (radialCompression (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • z.1)) j| ≤
        acceleratedHidingThreshold n k)
    (hy : ‖(acceleratedLengthScale L ε)⁻¹ • z.2‖ ≤ 2 * acceleratedDualRadius n k →
      ∀ j, t < acceleratedDualStage n j →
        |B ((acceleratedLengthScale L ε)⁻¹ • z.2) j| ≤ acceleratedHidingThreshold n k) :
    actualJointGradient (acceleratedRawPhysical A B L ε) z = acceleratedPrefixReply A B L ε (t + 1) z :=
  actualJointGradient_eventuallyEq (acceleratedRawPhysical_prefix_eventuallyEq A B hB hn hk L ε z hx hy)

theorem acceleratedPrefixReply_paper
    (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx) (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (z : Joint dx dy)
    (hx : ∀ j, t < acceleratedPrimalStage n j →
      |compressedCoordinates U 1 (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • z.1) j| ≤
        acceleratedHidingThreshold n k)
    (hy : ‖(acceleratedLengthScale L ε)⁻¹ • z.2‖ ≤ 2 * acceleratedDualRadius n k →
      ∀ j, t < acceleratedDualStage n j →
        |frameCoordinates V ((acceleratedLengthScale L ε)⁻¹ • z.2) j| ≤ acceleratedHidingThreshold n k) :
    acceleratedPrefixReply (frameCoordinates U) (frameCoordinates V) L ε (t + 1) z =
      (acceleratedPhysicalModel U V hn hk hL hε hμ hchain).jointGradient z := by
  have hx' : ∀ j, t < acceleratedPrimalStage n j →
      |frameCoordinates U (radialCompression (acceleratedPrimalRadius k)
        ((acceleratedLengthScale L ε)⁻¹ • z.1)) j| ≤ acceleratedHidingThreshold n k := by
    simpa only [compressedCoordinates, inv_one, one_smul] using hx
  have he := acceleratedRawPhysical_prefix_reply (frameCoordinates U) (frameCoordinates V)
    (frameCoordinates_norm_bound V) hn hk L ε z hx' hy
  rw [acceleratedRawPhysical_frame U V hn hk hL hε hμ hchain,
    actualJointGradient_objective] at he
  exact he.symm

end FreshGradientMinimax
