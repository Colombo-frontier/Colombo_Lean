import FreshGradientMinimax.AcceleratedLabelInteraction
import FreshGradientMinimax.AcceleratedPhysicalLocality

/-! On distinct labels and good queries, the actual exact-oracle
transcript equals the unstopped auxiliary transcript, including output. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem acceleratedLabelReply_paper {n k D t : ℕ}
    (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (hz : Function.Injective z)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (q : Joint D D)
    (hx : ∀ i, t < acceleratedPrimalStage n i →
      |radialCompression (acceleratedPrimalRadius k) ((acceleratedLengthScale L ε)⁻¹ • q.1)
        (acceleratedPrimalLabels z i)| ≤ acceleratedHidingThreshold n k)
    (hy : ‖(acceleratedLengthScale L ε)⁻¹ • q.2‖ ≤ 2 * acceleratedDualRadius n k →
      ∀ i, t < acceleratedDualStage n i →
        |((acceleratedLengthScale L ε)⁻¹ • q.2) (acceleratedDualLabels z i)| ≤ acceleratedHidingThreshold n k) :
    acceleratedLabelReply z L ε t q =
      (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
        hn hk hL hε hμ hchain).jointGradient q := by
  have he := acceleratedPrefixReply_paper (acceleratedPrimalLabelFrame hD z)
    (acceleratedDualLabelFrame hD z) hn hk hL hε hμ hchain q
    (by simpa only [compressedCoordinates, inv_one, one_smul,
      acceleratedPrimalLabelFrame_coordinates hD z hz, coordinateRead_apply] using hx)
    (by simpa only [acceleratedDualLabelFrame_coordinates hD z hz, coordinateRead_apply] using hy)
  simpa only [acceleratedLabelReply, acceleratedPrimalLabelFrame_coordinates hD z hz,
    acceleratedDualLabelFrame_coordinates hD z hz] using he

namespace Algorithm
variable {n k D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

theorem acceleratedLabel_output_identity (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (hz : Function.Injective z)
    (hn : 10 ≤ n + 2) (hk : 0 < k) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ L / (4 * acceleratedSmoothnessConstant * μ)) (H : ℕ) (seed : Seed)
    (hx : ∀ t < H, ∀ i, t < acceleratedPrimalStage n i →
      |radialCompression (acceleratedPrimalRadius k)
        ((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).1)
        (acceleratedPrimalLabels z i)| ≤ acceleratedHidingThreshold n k)
    (hy : ∀ t < H, ‖(acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2‖ ≤
      2 * acceleratedDualRadius n k → ∀ i, t < acceleratedDualStage n i →
        |((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2)
          (acceleratedDualLabels z i)| ≤ acceleratedHidingThreshold n k) :
    A.output H (A.deterministicRun (fun _ =>
      (acceleratedPhysicalModel (acceleratedPrimalLabelFrame hD z) (acceleratedDualLabelFrame hD z)
        hn hk hL hε hμ hchain).jointGradient) H seed) = A.acceleratedLabelOutput z L ε H seed := by
  apply A.first_exit_output_identity
  intro t ht
  exact (acceleratedLabelReply_paper hD z hz hn hk hL hε hμ hchain _ (hx t ht) (hy t ht)).symm

end Algorithm
end FreshGradientMinimax
