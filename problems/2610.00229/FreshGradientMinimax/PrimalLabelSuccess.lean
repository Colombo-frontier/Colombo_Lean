import FreshGradientMinimax.PrimalLabelDimension
import FreshGradientMinimax.FiniteEventIntegral

/-! Success on the actual hard instance requires either coin exhaustion or a
bad raw-label event, including the terminal output that was never queried. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped BigOperators
namespace Algorithm
variable {n D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def primalLabelCoinOutput (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) (sw : Seed × (Fin N → Bool)) : Euclid D :=
  A.output N (A.coinRun (primalCoinReply (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm σ) N sw.2 sw.1)

def primalLabelSuccessIndicator (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) (sw : Seed × (Fin N → Bool)) : ℝ :=
  truthValue (A.primalLabelCoinOutput hD z hL hε hμ hm σ N sw ∈
    (paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet ε)

theorem primalLabel_success_requires_bad (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) (sw : Seed × (Fin N → Bool))
    (hs : A.primalLabelCoinOutput hD z hL hε hμ hm σ N sw ∈
      (paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).successSet ε) :
    n ≤ coinSuccessCount sw.2 ∨ A.PrimalLabelBad L ε μ σ (coinRead sw.2) N sw.1 z := by
  classical
  by_cases hw : n ≤ coinSuccessCount sw.2
  · exact Or.inl hw
  right
  by_contra hb
  have hz : Function.Injective z := by
    by_contra h
    exact hb (Or.inl h)
  have hx : ∀ t < N, ∀ i : Fin (n + 1), coinPrefixCount (coinRead sw.2) t < i.val →
      |radialCompression (primalCompressionRadius n L ε)
        (A.primalLabelQuery z L ε μ σ (coinRead sw.2) t sw.1).1 (primalLabels z i)| ≤ primalLengthScale L ε / 4 := by
    intro t ht i hi
    apply le_of_not_gt
    intro hp
    exact hb (Or.inr (Or.inl ⟨⟨t, ht⟩, i.castAdd (n + n),
      by simpa only [primalLabelStage, Fin.addCases_left] using hi, hp⟩))
  have hy : ∀ t < N, ‖(A.primalLabelQuery z L ε μ σ (coinRead sw.2) t sw.1).2‖ <
        paperDualProtectionRadius n μ (primalValueScale L ε) →
      ∀ e : Fin n, coinPrefixCount (coinRead sw.2) t ≤ e.val →
        |(A.primalLabelQuery z L ε μ σ (coinRead sw.2) t sw.1).2 (dualLabels z (e.castAdd n))| ≤ primalLengthScale L ε ∧
        |(A.primalLabelQuery z L ε μ σ (coinRead sw.2) t sw.1).2 (dualLabels z (e.natAdd n))| ≤ primalLengthScale L ε := by
    intro t ht hn e he
    constructor
    · apply le_of_not_gt
      intro hp
      exact hb (Or.inr (Or.inr (Or.inl ⟨⟨t, ht⟩, (e.castAdd n).natAdd (n + 1),
        by simpa only [primalLabelStage, Fin.addCases_right, Fin.addCases_left] using Nat.lt_succ_of_le he,
        hn.le, hp⟩)))
    · apply le_of_not_gt
      intro hp
      exact hb (Or.inr (Or.inr (Or.inl ⟨⟨t, ht⟩, (e.natAdd n).natAdd (n + 1),
        by simpa only [primalLabelStage, Fin.addCases_right] using Nat.lt_succ_of_le he, hn.le, hp⟩)))
  have ho : |radialCompression (primalCompressionRadius n L ε)
      (A.primalLabelOutput z L ε μ σ (coinRead sw.2) N sw.1) (primalLabels z (Fin.last n))| ≤ primalLengthScale L ε / 4 := by
    apply le_of_not_gt
    intro hp
    exact hb (Or.inr (Or.inr (Or.inr ⟨(Fin.last n).castAdd (n + n),
      by simpa only [primalLabelStage, Fin.addCases_left, Fin.val_last, coinPrefixCount_word]
        using Nat.lt_of_not_ge hw, hp⟩)))
  have he := A.primalLabel_output_identity hD z hz hL hε hμ hm σ sw.2 (Nat.lt_of_not_ge hw) sw.1 hx hy
  have hg := A.primalLabel_output_barrier hD z hz hL hε hμ hm σ (coinRead sw.2) N sw.1 ho
  change ‖gradient (paperCompressedModel (primalLabelFrame hD z) (dualLabelFrame hD z) hL hε hμ hm).value
    (A.primalLabelCoinOutput hD z hL hε hμ hm σ N sw)‖ ≤ ε at hs
  rw [NCObjective.true_primal_gradient] at hs
  unfold primalLabelCoinOutput at hs
  rw [he] at hs
  linarith

theorem primalLabelSuccessIndicator_coupling (hD : (n + 1) + (n + n) ≤ D)
    (z : Fin ((n + 1) + (n + n)) → Fin D) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    (σ : ℝ) (N : ℕ) (sw : Seed × (Fin N → Bool)) :
    A.primalLabelSuccessIndicator hD z hL hε hμ hm σ N sw ≤ truthValue (n ≤ coinSuccessCount sw.2) +
      truthValue (A.PrimalLabelBad L ε μ σ (coinRead sw.2) N sw.1 z) :=
  (truthValue_mono (A.primalLabel_success_requires_bad hD z hL hε hμ hm σ N sw)).trans (truthValue_or_le _ _)

end Algorithm

theorem Algorithm.primalLabelSuccess_average (n N : ℕ) {L ε μ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ) (hm : μ ≤ L / (4 * primalScalingConstant))
    {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (primalLabelDimension n N L ε μ) (primalLabelDimension n N L ε μ) Seed)
    (σ : ℝ) (sw : Seed × (Fin N → Bool)) :
    (𝔼 z : Fin ((n + 1) + (n + n)) → Fin (primalLabelDimension n N L ε μ),
      A.primalLabelSuccessIndicator (primalLabelDimension_size n N L ε μ) z hL hε hμ hm σ N sw) ≤
      truthValue (n ≤ coinSuccessCount sw.2) + (1 / 12 : ℝ) := by
  have h := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ :
      Finset (Fin ((n + 1) + (n + n)) → Fin (primalLabelDimension n N L ε μ)))) =>
    A.primalLabelSuccessIndicator_coupling (primalLabelDimension_size n N L ε μ) z hL hε hμ hm σ N sw)
  rw [Finset.expect_add_distrib, Fintype.expect_const] at h
  exact h.trans (add_le_add_left (A.primalLabelBad_one_twelfth n N hL hε σ (coinRead sw.2) sw.1) _)

end FreshGradientMinimax
