import FreshGradientMinimax.PrimalResidualLemma
import FreshGradientMinimax.CoinCoupling
import FreshGradientMinimax.CoinProgress

/-! The concrete oracle (32), including zero noise, has exactly the output
law of a private seed independent of a finite iid Bernoulli word. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)

def primalCoinReply {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (c : Bool) (z : Joint dx dy) : Joint dx dy :=
  jointMaskedReply (primalRevealProbability L ε μ σ)
    (primalStaticBase U V hL hε hμ hm z) ((paperCompressedModel U V hL hε hμ hm).jointGradient z) c

theorem primalCoinReply_measurable {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (c : Bool) :
    Measurable (primalCoinReply U V hL hε hμ hm σ c) := by
  cases c
  · exact primalStaticBase_measurable U V hL hε hμ hm
  · exact jointMaskedReply_true_measurable _ _ _ (primalStaticBase_measurable U V hL hε hμ hm)
      (paperCompressedModel U V hL hε hμ hm).jointGradient_continuous.measurable

theorem primalFreshOracle_historyLaw {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)
    {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (N : ℕ) (seed : Seed) :
    A.historyKernel (primalFreshOracle U V hL hε hμ hm σ).kernel N seed =
      (coinWordLaw (primalRevealProbability L ε μ σ) N).map
        (fun w => A.coinRun (primalCoinReply U V hL hε hμ hm σ) N w seed) :=
  A.historyKernel_bernoulli_coin (primalRevealProbability_pos hL hε hμ σ).le
    (primalRevealProbability_le_one L ε μ σ) _ (primalCoinReply_measurable U V hL hε hμ hm σ) N seed

theorem primalFreshOracle_outputLaw {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)
    (ν : Measure Seed) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (hm : μ ≤ L / (4 * primalScalingConstant)) (σ : ℝ) (N : ℕ) :
    A.outputLaw ν (primalFreshOracle U V hL hε hμ hm σ).kernel N =
      (ν.prod (coinWordLaw (primalRevealProbability L ε μ σ) N)).map
        (fun z => A.output N (A.coinRun (primalCoinReply U V hL hε hμ hm σ) N z.2 z.1)) :=
  A.outputLaw_bernoulli_coin ν (primalRevealProbability_pos hL hε hμ σ).le
    (primalRevealProbability_le_one L ε μ σ) _ (primalCoinReply_measurable U V hL hε hμ hm σ) N

theorem primalFreshOracle_count_exhaustion {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hμ : 0 < μ)
    (σ : ℝ) {N : ℕ} (hn : 0 < n)
    (hN : (N : ℝ) ≤ (n : ℝ) / (12 * primalRevealProbability L ε μ σ)) :
    (coinWordLaw (primalRevealProbability L ε μ σ) N).real {w | n ≤ coinSuccessCount w} ≤ 1 / 12 :=
  coinSuccessCount_exhaustion (primalRevealProbability_pos hL hε hμ σ)
    (primalRevealProbability_le_one L ε μ σ) hn hN

end FreshGradientMinimax
