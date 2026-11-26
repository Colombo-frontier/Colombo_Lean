import Bilevel.MultiscaleRateProperty
import Bilevel.MultiscaleInnerCertifiedOracles
import Bilevel.BorelAdaptiveChannelTransport

/-! The macro-free execution in the common Euclidean full-query channel.
Encoding preserves the entire adaptive path, including infinite calls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.MultiscaleMean
open PrimitiveGeometry CompensatedMean BorelAdaptive ChiHierarchyHaar ChiHierarchyIndex SingleFrameSource
universe u v
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def unpackQuery (q : Joint E (LowerSpace E)) : InnerQuery E := (q.fst,q.snd)
def packReply (r : InnerReply E) : Joint E (LowerSpace E) × Joint E (LowerSpace E) :=
  (pack r.1.1 r.1.2,pack r.2.1 r.2.2)

section Measurable
variable [SecondCountableTopology E] [SecondCountableTopology (LowerSpace E)]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [MeasurableSpace (Joint E (LowerSpace E))] [BorelSpace (Joint E (LowerSpace E))]

omit [CompleteSpace E] [SecondCountableTopology E] in
theorem unpackQuery_measurable : Measurable (unpackQuery (E:=E)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E (LowerSpace E)).continuous.measurable

omit [CompleteSpace E] [SecondCountableTopology E] in
theorem packReply_measurable : Measurable (packReply (E:=E)) :=
  (packLinear.continuous.measurable.comp measurable_fst).prodMk
    (packLinear.continuous.measurable.comp measurable_snd)

end Measurable

def jointOriginalReply {n : ℕ} (P : Parameters (E:=E) n) (p : ℝ)
    (q : Joint E (LowerSpace E)) (c : Bool) := packReply (innerOriginalReply P p (unpackQuery q) c)

theorem jointOriginalReply_conservative {n : ℕ} (P : Parameters (E:=E) n) (p : ℝ) (c : Bool) :
    ∃ f g : Joint E (LowerSpace E) → ℝ,
      (∀ q,HasGradientAt f (jointOriginalReply P p q c).1 q) ∧
      (∀ q,HasGradientAt g (jointOriginalReply P p q c).2 q) := by
  let U := WithLp.prodContinuousLinearEquiv 2 ℝ E (LowerSpace E)
  let f := (fun z : InnerQuery E => P.data.upper z.1 z.2) ∘ U
  let g := (fun z : InnerQuery E => P.sampleLower p z.1 z.2 c) ∘ U
  have hf : Differentiable ℝ f :=
    (P.data.upper_joint_contDiff.comp U.contDiff).differentiable (by norm_num)
  have hg : Differentiable ℝ g :=
    ((P.sampleLower_joint_contDiff p c).comp U.contDiff).differentiable (by norm_num)
  have hfull (F : Joint E (LowerSpace E) → ℝ) (hF : Differentiable ℝ F)
      (q : Joint E (LowerSpace E)) (gx : E) (gy : LowerSpace E)
      (hx : HasGradientAt (fun x => F (pack x q.snd)) gx q.fst)
      (hy : HasGradientAt (fun y => F (pack q.fst y)) gy q.snd) :
      HasGradientAt F (pack gx gy) q := by
    have h := (hF q).hasGradientAt
    have hx' := (partial_x (gx:=(gradient F q).fst) (gy:=(gradient F q).snd)
      (x:=q.fst) (y:=q.snd) h).gradient
    have hy' := (partial_y (gx:=(gradient F q).fst) (gy:=(gradient F q).snd)
      (x:=q.fst) (y:=q.snd) h).gradient
    have he : gradient F q=pack gx gy := by
      apply (WithLp.equiv 2 (E × LowerSpace E)).injective
      exact Prod.ext (hx'.symm.trans hx.gradient) (hy'.symm.trans hy.gradient)
    rwa [he] at h
  refine ⟨f,g,?_,?_⟩
  · intro q
    exact hfull f hf q _ _ (P.data.upper_hasGradientX q.fst q.snd)
      (P.data.upper_hasGradientY q.fst q.snd)
  · intro q
    exact hfull g hg q _ _ (P.sampleLower_hasGradientX p q.fst q.snd c)
      (P.sampleLower_hasGradientY p q.fst q.snd c)

variable {n dim : ℕ}

theorem inner_rate_joint_channel
    (P : Parameters (E:=EuclideanGaussian.Space dim) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤dim)
    (p : ℝ) (hp1 : p≤1) (ε cost : ℝ)
    (H : InnerRateProperty.{u,v} P hD p hp1 ε cost)
    [MeasurableSpace (LowerSpace (EuclideanGaussian.Space dim))]
    [BorelSpace (LowerSpace (EuclideanGaussian.Space dim))]
    [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))]
    [BorelSpace (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))]
    {Private : Type u} {State : Type v} [MeasurableSpace Private] [MeasurableSpace State]
    (A : Program State (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim)))
      ((Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim))) ×
        (Joint (EuclideanGaussian.Space dim) (LowerSpace (EuclideanGaussian.Space dim))))
      (EuclideanGaussian.Space dim))
    (initial : Private → State) (hi : Measurable initial) (law : Measure Private) [IsProbabilityMeasure law]
    (hacc : ∀ a,(∫⁻ z,ENNReal.ofReal (innerFrameLoss P hD a
      (seededStopped A (fun a => jointOriginalReply (P.withFrame (frame hD a (Sum.inl ()))) p) initial (a,z)).2)
      ∂law.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ a,ENNReal.ofReal cost≤∫⁻ z,
      seededCalls A (fun a => jointOriginalReply (P.withFrame (frame hD a (Sum.inl ()))) p) initial (a,z)
      ∂law.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let original := fun a => jointOriginalReply (P.withFrame (frame hD a (Sum.inl ()))) p
  let encoded := innerFrameReply P p hD
  let A' := channelProgram A unpackQuery packReply unpackQuery_measurable packReply_measurable
  have hr : ∀ a q c,packReply (encoded a (unpackQuery q) c)=original a q c := fun _ _ _ => rfl
  have hacc' : ∀ a,(∫⁻ z,ENNReal.ofReal (Function.uncurry (innerFrameLoss P hD)
      (seededStopped A' encoded initial (a,z)))
      ∂law.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε := by
    intro a
    convert hacc a using 1
    apply lintegral_congr
    intro z
    rw [channel_seededStopped A unpackQuery packReply unpackQuery_measurable packReply_measurable
      original encoded hr initial (a,z)]
    rfl
  obtain ⟨a,ha⟩ := @H _ _ Private State _ _ A' initial hi law _ hacc'
  refine ⟨a,?_⟩
  convert ha using 1
  apply lintegral_congr
  intro z
  exact (channel_seededCalls A unpackQuery packReply unpackQuery_measurable packReply_measurable
    original encoded hr initial (a,z)).symm

end Bilevel.MultiscaleMean
