import Smoothness2601.FrameBoundary
import Smoothness2601.HardReply
import Smoothness2601.BoundaryOracle

/-! The boundary simulator replies are exactly the constructed upper-noise
oracle, with a frame-uniform measurable extension to truncated frames. -/
noncomputable section
namespace Smoothness2601.BoundaryInstance
open MeasureTheory ProbabilityTheory ExtensiveChain Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
variable (b : Budgets)

def revealRate (s : ℝ) : ℝ :=
  BernoulliOracle.revealProbability (s*(Cutoffs.frontierGradientBound+1)) b.σ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def compressedPoint (s : ℝ) (n : ℕ) (x : E) : E :=
  Bilevel.RadialWrapper.compress (chainRadius HardProfiles.radiusConstant n)
    ((s/spatialConstant b)⁻¹ • x)

def rawReply (s : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (query : Adaptive.Query E ℝ) (coin : Bool) : Joint E ℝ :=
  FrameBoundary.reply (chainRadius HardProfiles.radiusConstant n) chainAmplitude
    s (s/spatialConstant b) b.μ (revealRate b s) U query coin

omit [CompleteSpace E] in
theorem compressedPoint_continuous (s : ℝ) (n : ℕ) : Continuous (compressedPoint b (E := E) s n) :=
  (Bilevel.RadialWrapper.compress_contDiff _ 0).continuous.comp (continuous_const.smul continuous_id)

omit [CompleteSpace E] in
theorem compressedPoint_norm (s : ℝ) (n : ℕ) (x : E) :
    ‖compressedPoint b s n x‖ ≤ chainRadius HardProfiles.radiusConstant n :=
  Bilevel.RadialWrapper.compress_norm_le_radius _ (HardProfiles.radius_pos n) _

theorem rawReply_local (s : ℝ) {n : ℕ} (U : Fin (n+1) → E)
    (k : ℕ) (query : Adaptive.Query E ℝ) (coin : Bool)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |⟪compressedPoint b s n query.2.1,U i⟫| ≤ 1/16) :
    rawReply b s U query coin = rawReply b s
      (FrameTruncation.clip U (min (n+1) (k+if coin then 1 else 0))) query coin :=
  FrameBoundary.reply_local _ _ _ _ _ _ U k query coin
    (fun i hi => by simpa only [real_inner_comm,compressedPoint] using htail i hi)

theorem revealRate_pos {s : ℝ} (hs : 0 < s) : 0 < revealRate b s :=
  BernoulliOracle.revealProbability_pos
    (mul_pos hs (by linarith [frontierGradientBound_nonneg])) b.σ_pos

theorem revealRate_le_one {s : ℝ} (hs : 0 < s)
    (hsmall : s ≤ b.σ/(Cutoffs.frontierGradientBound+1)) : revealRate b s ≤ 1 :=
  BernoulliOracle.revealProbability_le_one
    (mul_pos hs (by linarith [frontierGradientBound_nonneg])).le b.σ_pos
    ((le_div_iff₀ (by linarith [frontierGradientBound_nonneg])).mp hsmall)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem rawReply_measurable (s : ℝ) (n : ℕ) :
    Measurable (fun z : (Fin (n+1) → E) × (Adaptive.Query E ℝ × Bool) =>
      rawReply b s z.1 z.2.1 z.2.2) :=
  FrameBoundary.reply_measurable _ _ _ _ _ _ n

variable {b} {s : ℝ} (hs : 0 < s) (hμL : b.μ ≤ b.L₁)
  {n : ℕ} (U : Fin (n+1) → E) (hU : Orthonormal ℝ U)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rawReply_sample (query : Adaptive.Query E ℝ) (coin : Bool) :
    rawReply b s U query coin =
      FreshUpperBernoulli.sample (population (FrameTruncation.frameIsometry U hU) hs hμL)
        (fun query => signalField (b := b) (FrameTruncation.frameIsometry U hU) hs query.2.1)
        (revealRate b s) query coin := by
  let V := FrameTruncation.frameIsometry U hU
  let F := HardProfiles.profiles V
  have he : (s^2/spatialConstant b)/(s/spatialConstant b) = s := by
    have := (spatialConstant_pos b).ne'
    field_simp
    ring
  rcases query with ⟨flag,x,y⟩
  cases flag
  · rw [FreshUpperBernoulli.sample_upper]
    have hu : Adaptive.trueGradient (population V hs hμL) (false,(x,y)) =
        pack (s • F.gA ((s/spatialConstant b)⁻¹ • x)+s • F.gB ((s/spatialConstant b)⁻¹ • x)) 0 := by
      change pack (((s^2/spatialConstant b)/(s/spatialConstant b)) •
        (F.gA ((s/spatialConstant b)⁻¹ • x)+F.gB ((s/spatialConstant b)⁻¹ • x))) 0 = _
      rw [he,smul_add]
    change _ = BernoulliOracle.response (revealRate b s)
      (Adaptive.trueGradient (population V hs hμL) (false,(x,y))-
        signalField (b := b) V hs x) (signalField (b := b) V hs x) coin
    rw [hu]
    apply (WithLp.equiv 2 (E × ℝ)).injective
    apply Prod.ext
    · change s • _+(if coin then (revealRate b s)⁻¹ else 0) • (s • _) =
        (s • _+s • _-s • _)+(if coin then (revealRate b s)⁻¹ else 0) • (s • _)
      abel
    · cases coin <;> simp [rawReply,FrameBoundary.reply,Bilevel.BernoulliOracle.sample,signalField,pack]
  · change pack (0:E) (b.μ*y) =
      SineGeometry.lowerGradient (fun _ => 0) (fun _ => (s/spatialConstant b)⁻¹ • (0:E))
        b.μ 0 1 (pack x y)+(0:ℝ) • _
    simp [SineGeometry.lowerGradient,SineLift.lowerGradient,pack]

theorem rawReply_oracle_law (hsmall : s ≤ b.σ/(Cutoffs.frontierGradientBound+1))
    (hq1 : revealRate b s ≤ 1) (query : Adaptive.Query E ℝ) :
    (oracle (FrameTruncation.frameIsometry U hU) hs hμL hsmall).law (query,()) =
      (BernoulliOracle.law (revealRate b s) hq1).map
        (fun coin => (rawReply b s U query coin,())) := by
  let V := FrameTruncation.frameIsometry U hU
  have hm := FreshUpperBernoulli.sample_measurable (population V hs hμL)
    (signal (b := b) V hs) (signal_measurable (b := b) V hs) (revealRate b s)
  change FiniteSampleOracle.law (BernoulliOracle.law (revealRate b s) hq1)
    (FreshUpperBernoulli.sample (population V hs hμL) (signal (b := b) V hs) (revealRate b s)) (query,()) = _
  rw [FiniteSampleOracle.law_apply _ _ hm]
  congr 1
  funext coin
  exact congrArg (fun v => (v,())) (rawReply_sample hs hμL U hU query coin).symm

end Smoothness2601.BoundaryInstance
