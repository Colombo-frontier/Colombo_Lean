import FreshGradientMinimax.PrimalLabelInteraction
import FreshGradientMinimax.CompressionScaling

/-! Collision-free raw labels give legal instances. Their real fresh-coin
outputs agree with the auxiliary outputs on the explicit hidden-coordinate event. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

def primalLabelFrame {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) : Euclid (n + 1) →ₗᵢ[ℝ] Euclid D :=
  labelFrame (by omega) (primalLabels z)

def dualLabelFrame {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) : Euclid (n + n) →ₗᵢ[ℝ] Euclid D :=
  labelFrame (by omega) (dualLabels z)

theorem primalLabelFrame_coordinates {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z) :
    frameCoordinates (primalLabelFrame hD z) = coordinateRead (primalLabels z) := by
  rw [primalLabelFrame, labelFrame_of_injective _ _ (primalLabels_injective hz), coordinateFrame_coordinates]

theorem dualLabelFrame_coordinates {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z) :
    frameCoordinates (dualLabelFrame hD z) = coordinateRead (dualLabels z) := by
  rw [dualLabelFrame, labelFrame_of_injective _ _ (dualLabels_injective hz), coordinateFrame_coordinates]

theorem primalLabelFrame_small {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z)
    {r : ℝ} (hr : 0 < r) (R : ℝ) (x : Euclid D) (i : Fin (n + 1))
    (hi : |radialCompression R x (primalLabels z i)| ≤ r / 4) :
    |compressedCoordinates (primalLabelFrame hD z) r R x i| ≤ 1 / 4 := by
  simp only [compressedCoordinates, primalLabelFrame_coordinates hD z hz, PiLp.smul_apply,
    coordinateRead_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr]
  have h := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
  have he : r⁻¹ * (r / 4) = 1 / 4 := by field_simp
  exact h.trans_eq he

theorem primalLabelReply_paper {n D : ℕ} (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (c : ℕ → Bool) (t : ℕ)
    (hk : coinPrefixCount c t < n + 1) (q : Joint D D)
    (hx : ∀ i : Fin (n + 1), coinPrefixCount c t < i.val →
      |radialCompression (primalCompressionRadius n L ε) q.1 (primalLabels z i)| ≤ primalLengthScale L ε / 4)
    (hy : ‖q.2‖ < paperDualProtectionRadius n μ (primalValueScale L ε) →
      ∀ e : Fin n, coinPrefixCount c t ≤ e.val →
        |q.2 (dualLabels z (e.castAdd n))| ≤ primalLengthScale L ε ∧
        |q.2 (dualLabels z (e.natAdd n))| ≤ primalLengthScale L ε) :
    primalLabelReply z L ε μ σ c t q =
      primalCoinReply (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm σ (c t) q := by
  have h := primalRawAuxiliaryReply_paper (primalLabelFrame hD z) (dualLabelFrame hD z)
    hL hε hμ hm σ ⟨coinPrefixCount c t, hk⟩ (c t) q
    (fun i hi => primalLabelFrame_small hD z hz (primalLengthScale_pos hL hε) _ q.1 i (hx i hi))
    (by simpa only [dualLabelFrame_coordinates hD z hz, coordinateRead_apply] using hy)
  rw [primalLabelFrame_coordinates hD z hz, dualLabelFrame_coordinates hD z hz] at h
  exact h

namespace Algorithm
variable {n D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

theorem primalLabel_output_identity (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) {N : ℕ} (w : Fin N → Bool)
    (hw : coinSuccessCount w < n) (seed : Seed)
    (hx : ∀ t < N, ∀ i : Fin (n + 1), coinPrefixCount (coinRead w) t < i.val →
      |radialCompression (primalCompressionRadius n L ε)
        (A.primalLabelQuery z L ε μ σ (coinRead w) t seed).1 (primalLabels z i)| ≤ primalLengthScale L ε / 4)
    (hy : ∀ t < N, ‖(A.primalLabelQuery z L ε μ σ (coinRead w) t seed).2‖ <
        paperDualProtectionRadius n μ (primalValueScale L ε) →
      ∀ e : Fin n, coinPrefixCount (coinRead w) t ≤ e.val →
        |(A.primalLabelQuery z L ε μ σ (coinRead w) t seed).2 (dualLabels z (e.castAdd n))| ≤ primalLengthScale L ε ∧
        |(A.primalLabelQuery z L ε μ σ (coinRead w) t seed).2 (dualLabels z (e.natAdd n))| ≤ primalLengthScale L ε) :
    A.output N (A.coinRun (primalCoinReply (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm σ) N w seed) =
      A.primalLabelOutput z L ε μ σ (coinRead w) N seed := by
  apply A.coin_first_exit_output_identity
  intro t ht
  exact (primalLabelReply_paper hD z hz hL hε hμ hm σ (coinRead w) t
    (lt_trans (lt_of_le_of_lt (coinPrefixCount_word_le w ht.le) hw) (Nat.lt_succ_self n)) _
    (hx t ht) (hy t ht)).symm

theorem primalLabel_output_barrier (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (hz : Function.Injective z)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (c : ℕ → Bool) (N : ℕ) (seed : Seed)
    (hx : |radialCompression (primalCompressionRadius n L ε)
      (A.primalLabelOutput z L ε μ σ c N seed) (primalLabels z (Fin.last n))| ≤ primalLengthScale L ε / 4) :
    2 * ε ≤ ‖(paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).primalGradient
      (A.primalLabelOutput z L ε μ σ c N seed)‖ :=
  paperCompressedModel_barrier (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm _
    (primalLabelFrame_small hD z hz (primalLengthScale_pos hL hε) _ _ (Fin.last n) hx)

end Algorithm
end FreshGradientMinimax
