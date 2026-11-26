import FreshGradientMinimax.PrimalTruncation
import FreshGradientMinimax.StaticTruncation

/-! Equation (30) as a static measurable selection of ordinary fixed-index
gradients, and the actual fixed fresh-gradient kernel of (31)--(32). -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def coreDualStageCoordinates {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (y : Euclid dy) : Fin (n + 1) → Bool → ℝ :=
  Fin.cases (fun _ => 0) (fun e b => if b then frameCoordinates V y (e.castAdd n)
    else frameCoordinates V y (e.natAdd n))

theorem coreDualStageCoordinates_succ {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (y : Euclid dy) (e : Fin n) :
    coreDualStageCoordinates V y e.succ true = frameCoordinates V y (e.castAdd n) ∧
    coreDualStageCoordinates V y e.succ false = frameCoordinates V y (e.natAdd n) := by
  simp [coreDualStageCoordinates]

theorem coreDualStageCoordinates_continuous {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (i : Fin (n + 1)) (b : Bool) : Continuous (fun y => coreDualStageCoordinates V y i b) := by
  refine Fin.cases ?_ (fun e => ?_) i
  · exact continuous_const
  · cases b
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (e.natAdd n)).continuous.comp (frameCoordinates V).continuous
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (e.castAdd n)).continuous.comp (frameCoordinates V).continuous

variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)

def primalStaticIndex (L ε : ℝ) (z : Joint dx dy) : Fin (n + 1) :=
  thresholdStageIndex (primalLengthScale L ε)
    (fun i => compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i)
    (coreDualStageCoordinates V z.2)

theorem primalStaticIndex_measurable (L ε : ℝ) : Measurable (primalStaticIndex U V L ε) := by
  apply thresholdStageIndex_measurable
  · intro i
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      ((compressedCoordinates_contDiff U (k := 1) _ _).continuous.comp continuous_fst)).measurable
  · intro i b
    exact ((coreDualStageCoordinates_continuous V i b).comp continuous_snd).measurable

theorem primalStaticIndex_hidden (L ε : ℝ) (z : Joint dx dy) :
    (∀ i : Fin (n + 1), (primalStaticIndex U V L ε z).val < i.val →
      |compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i| ≤ 1 / 4) ∧
    (∀ e : Fin n, (primalStaticIndex U V L ε z).val ≤ e.val →
      |frameCoordinates V z.2 (e.castAdd n)| ≤ primalLengthScale L ε ∧
      |frameCoordinates V z.2 (e.natAdd n)| ≤ primalLengthScale L ε) := by
  constructor
  · intro i hi
    exact (thresholdStage_hidden _ _ _ i hi).1
  · intro e he
    have hi : (primalStaticIndex U V L ε z).val < e.succ.val := by change _ < e.val + 1; omega
    have h := (thresholdStage_hidden (primalLengthScale L ε)
      (fun i => compressedCoordinates U (primalLengthScale L ε) (primalCompressionRadius n L ε) z.1 i)
      (coreDualStageCoordinates V z.2) e.succ hi).2
    simpa only [(coreDualStageCoordinates_succ V z.2 e).1, (coreDualStageCoordinates_succ V z.2 e).2] using h

def primalStaticBase {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (z : Joint dx dy) : Joint dx dy :=
  (paperTruncatedModel U V hL hε hμ hm ((primalStaticIndex U V L ε z).val + 1)).jointGradient z

theorem primalStaticBase_measurable {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) : Measurable (primalStaticBase U V hL hε hμ hm) :=
  measurable_selected_truncation _ (primalStaticIndex_measurable U V L ε)
    (fun k => (paperTruncatedModel U V hL hε hμ hm (k.val + 1)).jointGradient)
    (fun k => (paperTruncatedModel U V hL hε hμ hm (k.val + 1)).jointGradient_continuous.measurable)

theorem primalStaticBase_residual_sq {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (z : Joint dx dy) :
    jointNormSq ((paperCompressedModel U V hL hε hμ hm).jointGradient z -
      primalStaticBase U V hL hε hμ hm z) ≤ (10 ^ 4 * primalInteractionScale L ε μ) ^ 2 :=
  paperTruncatedModel_joint_residual U V hL hε hμ hm (primalStaticIndex U V L ε z) z
    (primalStaticIndex_hidden U V L ε z).1 (primalStaticIndex_hidden U V L ε z).2

theorem primalStaticBase_residual_norm {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (z : Joint dx dy) :
    Real.sqrt (jointNormSq ((paperCompressedModel U V hL hε hμ hm).jointGradient z -
      primalStaticBase U V hL hε hμ hm z)) ≤ 10 ^ 4 * primalInteractionScale L ε μ := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨mul_nonneg (by norm_num) (primalInteractionScale_pos hL hε hμ).le,
    primalStaticBase_residual_sq U V hL hε hμ hm z⟩

def primalRevealProbability (L ε μ σ : ℝ) : ℝ :=
  revealProbability ((10 ^ 4 * primalInteractionScale L ε μ) ^ 2) (σ ^ 2)

def primalFreshOracle {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) :
    FreshOracle (paperCompressedModel U V hL hε hμ hm) σ :=
  FreshOracle.masked (paperCompressedModel U V hL hε hμ hm) σ
    ((10 ^ 4 * primalInteractionScale L ε μ) ^ 2)
    (sq_pos_of_pos (mul_pos (by norm_num) (primalInteractionScale_pos hL hε hμ)))
    (primalStaticBase U V hL hε hμ hm) (primalStaticBase_measurable U V hL hε hμ hm)
    (primalStaticBase_residual_sq U V hL hε hμ hm)

theorem primalFreshOracle_kernel {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) :
    (primalFreshOracle U V hL hε hμ hm σ).kernel =
      maskedGradientKernel (primalRevealProbability L ε μ σ) (primalStaticBase U V hL hε hμ hm)
        (paperCompressedModel U V hL hε hμ hm).jointGradient
        (primalStaticBase_measurable U V hL hε hμ hm)
        (paperCompressedModel U V hL hε hμ hm).jointGradient_continuous.measurable := rfl

theorem primalFreshOracle_zero {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) :
    (primalFreshOracle U V hL hε hμ hm 0).kernel =
      (FreshOracle.exact (paperCompressedModel U V hL hε hμ hm) 0).kernel :=
  FreshOracle.masked_zero_kernel _ _ _ _ _ _

end FreshGradientMinimax
