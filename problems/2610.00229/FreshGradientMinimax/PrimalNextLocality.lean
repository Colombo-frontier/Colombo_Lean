import FreshGradientMinimax.CoreNextLocality
import FreshGradientMinimax.PrimalExterior

/-! The actual compressed gradient is fully determined by one additional
stage on the good primal event. The static index cannot jump past hidden bounds. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)

theorem paperTruncatedModel_full_gradient {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (z : Joint dx dy) :
    (paperTruncatedModel U V hL hε hμ hm (n + 1)).jointGradient z =
      (paperCompressedModel U V hL hε hμ hm).jointGradient z := by
  change (compressedGradX U (paperTruncatedCore V μ (primalValueScale L ε) (n + 1)) _ _ _ z.1 z.2,
      compressedGradY U (paperTruncatedCore V μ (primalValueScale L ε) (n + 1)) _ _ z.1 z.2) = _
  rw [paperTruncatedCore_full]
  rfl

theorem paperTruncatedModel_next_gradient {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (k : Fin (n + 1)) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4) :
    (paperTruncatedModel U V hL hε hμ hm (min (k.val + 2) (n + 1))).jointGradient z =
      (paperCompressedModel U V hL hε hμ hm).jointGradient z := by
  by_cases hk : k.val = n
  · rw [hk, Nat.min_eq_right (by omega)]
    exact paperTruncatedModel_full_gradient U V hL hε hμ hm z
  · rw [Nat.min_eq_left (by omega)]
    have h := truncatedCore_next_gradients_eq V hμ
      (Real.sqrt_pos.mpr (div_pos (primalValueScale_pos hL hε) hμ)) k.val _ z.2 hu
    apply Prod.ext
    · change compressedGradX U _ _ _ _ z.1 z.2 = compressedGradX U _ _ _ _ z.1 z.2
      unfold compressedGradX paperCoreObjective paperTruncatedCore
      rw [h.1]
    · exact h.2

theorem primalStaticIndex_le {L ε : ℝ} (k : ℕ) (z : Joint dx dy)
    (hu : ∀ i : Fin (n + 1), k < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4)
    (hy : ∀ e : Fin n, k ≤ e.val →
      |frameCoordinates V z.2 (e.castAdd n)| ≤ primalLengthScale L ε ∧
      |frameCoordinates V z.2 (e.natAdd n)| ≤ primalLengthScale L ε) :
    (primalStaticIndex U V L ε z).val ≤ k := by
  apply thresholdStage_at_most
  intro i hi
  refine ⟨hu i hi, ?_⟩
  revert hi
  refine Fin.cases ?_ (fun e => ?_) i
  · intro hi
    exact (Nat.not_lt_zero k hi).elim
  · intro hi
    have he : k ≤ e.val := by change k < e.val + 1 at hi; omega
    simpa only [(coreDualStageCoordinates_succ V z.2 e).1,
      (coreDualStageCoordinates_succ V z.2 e).2] using hy e he

theorem primalCoinReply_next_prefix {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (k : Fin (n + 1)) (z : Joint dx dy) (c : Bool)
    (hu : ∀ i : Fin (n + 1), k.val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4) :
    primalCoinReply U V hL hε hμ hm σ c z =
      jointMaskedReply (primalRevealProbability L ε μ σ) (primalStaticBase U V hL hε hμ hm z)
        ((paperTruncatedModel U V hL hε hμ hm (min (k.val + 2) (n + 1))).jointGradient z) c := by
  rw [paperTruncatedModel_next_gradient U V hL hε hμ hm k z hu]
  rfl

end FreshGradientMinimax
