import FreshGradientMinimax.AcceleratedLabelDimension
import FreshGradientMinimax.AcceleratedLabelCoupling
import FreshGradientMinimax.FiniteEventIntegral

/-! Every successful actual exact-oracle output requires a bad label
event. No restriction is imposed on the algorithm's final output. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
namespace Algorithm
variable {n k D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def acceleratedLabelActualOutput (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (H : ℕ) (seed : Seed) : Euclid D :=
  A.output H (A.deterministicRun (fun _ =>
    (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
      hn hk hL hε hμ hchain).jointGradient) H seed)

def acceleratedLabelSuccessIndicator (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (H : ℕ) (seed : Seed) : ℝ :=
  truthValue (A.acceleratedLabelActualOutput hD z hn hk hL hε hμ hchain H seed ∈
    (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
      hn hk hL hε hμ hchain).successSet ε)

theorem acceleratedLabel_success_requires_bad (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ))
    (H : ℕ) (hH : 2 * H + 2 ≤ acceleratedStageCount n k) (seed : Seed)
    (hs : A.acceleratedLabelActualOutput hD z hn hk hL hε hμ hchain H seed ∈
      (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
        hn hk hL hε hμ hchain).successSet ε) : A.AcceleratedLabelBad L ε H seed z := by
  classical
  by_contra hb
  have hz : Function.Injective z := by
    by_contra h
    exact hb (Or.inl h)
  have hx : ∀ t < H, ∀ i, t < acceleratedPrimalStage n i →
      |radialCompression (acceleratedPrimalRadius k)
        ((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).1)
        (acceleratedPrimalLabels z i)| ≤ acceleratedHidingThreshold n k := by
    intro t ht i hi
    apply le_of_not_gt
    intro hp
    exact hb (Or.inr (Or.inl ⟨⟨t, ht⟩, i.castAdd (k * (n + 2)),
      by simpa only [acceleratedLabelStage, Fin.addCases_left] using hi, hp⟩))
  have hy : ∀ t < H, ‖(acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2‖ ≤
      2 * acceleratedDualRadius n k → ∀ i, t < acceleratedDualStage n i →
        |((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2)
          (acceleratedDualLabels z i)| ≤ acceleratedHidingThreshold n k := by
    intro t ht hy i hi
    apply le_of_not_gt
    intro hp
    exact hb (Or.inr (Or.inr (Or.inl ⟨⟨t, ht⟩, i.natAdd (k * 2 + 1),
      by simpa only [acceleratedLabelStage, Fin.addCases_right] using hi, hy, hp⟩)))
  let j : Fin (k * 2 + 1) := interleavedZ (⟨k - 1, by omega⟩ : Fin k)
  have hj : H < acceleratedPrimalStage n j := acceleratedStages_terminal_hidden n hk hH
  have ho : |radialCompression (acceleratedPrimalRadius k)
      ((acceleratedLengthScale L ε)⁻¹ • A.acceleratedLabelOutput z L ε H seed)
        (acceleratedPrimalLabels z j)| ≤ acceleratedHidingThreshold n k := by
    apply le_of_not_gt
    intro hp
    exact hb (Or.inr (Or.inr (Or.inr ⟨j.castAdd (k * (n + 2)),
      by simpa only [acceleratedLabelStage, Fin.addCases_left] using hj, hp⟩)))
  have hout : |compressedCoordinates (acceleratedPrimalLabelFrame hD z) 1 (acceleratedPrimalRadius k)
      ((acceleratedLengthScale L ε)⁻¹ • A.acceleratedLabelOutput z L ε H seed) j| ≤ 1 / 4 := by
    simpa only [compressedCoordinates, inv_one, one_smul, acceleratedPrimalLabelFrame_coordinates hD z hz,
      coordinateRead_apply] using ho.trans (acceleratedHidingThreshold_lt_quarter n hk).le
  have hg := acceleratedPhysicalModel_barrier (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
    hn hk hL hε hμ hchain (A.acceleratedLabelOutput z L ε H seed) hout
  have he := A.acceleratedLabel_output_identity hD z hz hn hk hL hε hμ hchain H seed hx hy
  change ‖gradient (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z)
    (acceleratedDualLabelFrame hD z) hn hk hL hε hμ hchain).value
    (A.acceleratedLabelActualOutput hD z hn hk hL hε hμ hchain H seed)‖ ≤ ε at hs
  rw [NCObjective.true_primal_gradient] at hs
  unfold acceleratedLabelActualOutput at hs
  rw [he] at hs
  linarith only [hg, hs, hε]

theorem acceleratedLabelSuccessIndicator_coupling (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ))
    (H : ℕ) (hH : 2 * H + 2 ≤ acceleratedStageCount n k) (seed : Seed) :
    A.acceleratedLabelSuccessIndicator hD z hn hk hL hε hμ hchain H seed ≤
      truthValue (A.AcceleratedLabelBad L ε H seed z) :=
  truthValue_mono (A.acceleratedLabel_success_requires_bad hD z hn hk hL hε hμ hchain H hH seed)

end Algorithm

theorem Algorithm.acceleratedLabelSuccess_average (n k H : ℕ) (hn : 10 ≤ n + 2) (hk : 0 < k)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ))
    (hH : 2 * H + 2 ≤ acceleratedStageCount n k) {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (acceleratedLabelDimension n k H) (acceleratedLabelDimension n k H) Seed) (seed : Seed) :
    (𝔼 z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H),
      A.acceleratedLabelSuccessIndicator (acceleratedLabelDimension_size n k H) z hn hk hL hε hμ hchain H seed) ≤ (1 / 12 : ℝ) := by
  have h := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ :
      Finset (Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H)))) =>
    A.acceleratedLabelSuccessIndicator_coupling (acceleratedLabelDimension_size n k H) z hn hk hL hε hμ hchain H hH seed)
  exact h.trans (A.acceleratedLabelBad_one_twelfth n k H hk L ε seed)

end FreshGradientMinimax
