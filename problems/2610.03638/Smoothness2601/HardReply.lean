import Smoothness2601.FrameResponse
import Smoothness2601.HardInstance

/-! The raw-frame simulator uses exactly the verified source Population's
fresh oracle, including all amplitude and spatial rescalings. -/
noncomputable section
namespace Smoothness2601.HardProfiles
open ExtensiveChain Bilevel.PrimitiveGeometry
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def revealRate (p : WithTop ℕ) (s : ℝ) : ℝ :=
  BernoulliOracle.revealProbability (W.signalConstant*s*sineWidth p β s W.K) b.σ

def compressedPoint (s : ℝ) (n : ℕ) (x : E) : E :=
  Bilevel.RadialWrapper.compress (chainRadius radiusConstant n) ((s/W.τ)⁻¹ • x)

def rawReply (p : WithTop ℕ) (s : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (query : Adaptive.Query E ℝ) (coin : Bool) : Joint E ℝ :=
  FrameTruncation.reply (chainRadius radiusConstant n) chainAmplitude (s^2/W.τ) (s/W.τ)
    W.c W.m (s^2/(W.τ*W.c)) (sineWidth p β s W.K) (revealRate W p s) U query coin

theorem radius_pos (n : ℕ) : 0 < chainRadius radiusConstant n := by
  unfold chainRadius
  have := radiusConstant_ge_one
  positivity

theorem radius_ge_delta (n : ℕ) : (1/16 : ℝ) ≤ chainRadius radiusConstant n := by
  have hn : (1:ℝ) ≤ Real.sqrt ((n:ℝ)+1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hc := radiusConstant_ge_one
  unfold chainRadius
  nlinarith

omit [CompleteSpace E] in
omit [CompleteSpace E] in
theorem compressedPoint_continuous (s : ℝ) (n : ℕ) : Continuous (compressedPoint W (E := E) s n) :=
  (Bilevel.RadialWrapper.compress_contDiff _ 0).continuous.comp (continuous_const.smul continuous_id)

omit [CompleteSpace E] in
omit [CompleteSpace E] in
theorem compressedPoint_norm (s : ℝ) (n : ℕ) (x : E) :
    ‖compressedPoint W s n x‖ ≤ chainRadius radiusConstant n :=
  Bilevel.RadialWrapper.compress_norm_le_radius _ (radius_pos n) _

theorem rawReply_local (p : WithTop ℕ) (s : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (k : ℕ) (query : Adaptive.Query E ℝ) (coin : Bool)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |⟪compressedPoint W s n query.2.1,U i⟫| ≤ 1/16) :
    rawReply W p s U query coin = rawReply W p s
      (FrameTruncation.clip U (min (n+1) (k+if coin then 1 else 0))) query coin :=
  FrameTruncation.reply_local _ _ _ _ _ _ _ _ _ U k query coin
    (fun i hi => by simpa only [real_inner_comm,compressedPoint] using htail i hi)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem rawReply_measurable (p : WithTop ℕ) (s : ℝ) (n : ℕ) :
    Measurable (fun z : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      rawReply W p s z.1 z.2.1 z.2.2) :=
  FrameTruncation.reply_measurable _ _ _ _ _ _ _ _ _ n

variable {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)
  {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U)

include hp hβ hs hsδ in
include hp hβ hs hsδ in
theorem revealRate_pos : 0 < revealRate W p s :=
  BernoulliOracle.revealProbability_pos
    (mul_pos (mul_pos W.signalConstant_pos hs)
      (sineWidth_pos hp hβ W.K_pos hs (W.threshold_conditions hsδ).2.1)) b.σ_pos

include hp hβ hs hsδ in
include hp hβ hs hsδ in
theorem revealRate_le_one : revealRate W p s ≤ 1 :=
  BernoulliOracle.revealProbability_le_one
    (mul_pos (mul_pos W.signalConstant_pos hs)
      (sineWidth_pos hp hβ W.K_pos hs (W.threshold_conditions hsδ).2.1)).le b.σ_pos
    (W.signal_small hs hsδ
      (sineWidth_bounds hp hβ hs (W.threshold_conditions hsδ).2.1 W.K_pos).2)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rawReply_sample (query : Adaptive.Query E ℝ) (coin : Bool) :
    rawReply W p s U query coin =
      FreshBernoulli.sample (population W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU))
        (fun query => ((profiles (FrameTruncation.frameIsometry U hU)).sourceScaled W.τ_pos hs).signal
          W.m (s^2/(W.τ*W.c)) (sineWidth p β s W.K) (pack query.2.1 query.2.2))
        (revealRate W p s) query coin :=
  FrameTruncation.reply_eq_scaled_sample U hU (div_nonneg (sq_nonneg s) W.τ_pos.le)
    (div_pos hs W.τ_pos) (calibration W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU))
    (revealRate W p s) query coin

theorem rawReply_oracle_law (hq1 : revealRate W p s ≤ 1) (query : Adaptive.Query E ℝ) :
    (oracle W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU)).law (query,()) =
      (BernoulliOracle.law (revealRate W p s) hq1).map
        (fun coin => (rawReply W p s U query coin,())) := by
  let F := (profiles (FrameTruncation.frameIsometry U hU)).sourceScaled W.τ_pos hs
  let S := calibration W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU)
  have hsignal : Measurable (fun query : Adaptive.Query E ℝ =>
      F.signal S.m S.a S.h (pack query.2.1 query.2.2)) :=
    (F.signal_continuous S).measurable.comp
      ((packLinear (X := E) (Y := ℝ)).continuous.measurable.comp measurable_snd)
  change FreshBernoulli.law (F.population S) _ _ _ (query,()) = _
  rw [FreshBernoulli.law_apply _ _ hsignal]
  congr 1
  funext coin
  exact congrArg (fun v => (v,())) (rawReply_sample W hp hβ hs hsδ U hU query coin).symm

end Smoothness2601.HardProfiles
