import Bilevel.PartialLegendreConservative
import Bilevel.PartialLegendreJointInverse
import Bilevel.FreshOracle

/-! Measurable fresh-sample oracle for the fixed conjugate sample functions.
The actual adaptive error is conditionally centered with respect to the whole
entering past, and its second moment is controlled independently of that past. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PartialLegendre.ConjugateOracle
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G G₀ : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hG₀ : LipschitzWith δ G₀) (hδ : δ<1)

theorem jointGradient_continuous : Continuous (jointGradient hG hδ) := by
  rw [show jointGradient hG hδ=(fun v => lowerProjection v-G (jointInverse hG hδ v)) from
    funext (jointGradient_representation hG hδ)]
  exact (lowerProjection : Joint X Y →L[ℝ] Joint X Y).continuous.sub
    (hG.continuous.comp (jointInverse_continuous hG hδ))

variable (C : Joint X Y → Joint X Y) (hC : Continuous C)
include hC

theorem meanGradient_continuous (m : ℝ) : Continuous (meanGradient hG hδ m C) :=
  ((jointGradient_continuous hG hδ).const_smul m).add hC

variable [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)]

theorem sampleGradient_measurable (m p : ℝ) :
    Measurable (fun qb : Joint X Y × Bool => sampleGradient hG hG₀ hδ m p C qb.2 qb.1) := by
  have hb : Measurable (fun qb : Joint X Y × Bool => meanGradient hG₀ hδ m C qb.1) :=
    (meanGradient_continuous hG₀ hδ C hC m).measurable.comp measurable_fst
  have hs : Measurable (fun qb : Joint X Y × Bool =>
      m • (jointGradient hG hδ qb.1-jointGradient hG₀ hδ qb.1)) :=
    (((jointGradient_continuous hG hδ).sub (jointGradient_continuous hG₀ hδ)).const_smul m).measurable.comp measurable_fst
  have hc : Measurable (fun qb : Joint X Y × Bool => if qb.2 then p⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then p⁻¹ else (0:ℝ))).comp measurable_snd
  exact hb.add (hc.smul hs)

def freshOracle {m η B σ : ℝ} (hm : 0≤m) (hB : 0<B)
    (hdiff : ∀ v,‖G v-G₀ v‖≤η)
    (henv : (Real.sqrt 2*m/(1-(δ:ℝ)))*η≤B) :
    FreshOracle.Oracle (Query := Joint X Y) (E := Joint X Y)
      (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ where
  truth := meanGradient hG hδ m C
  sample := fun q b => sampleGradient hG hG₀ hδ m (BernoulliOracle.probability B σ) C b q
  truth_measurable := (meanGradient_continuous hG hδ C hC m).measurable
  sample_measurable := sampleGradient_measurable hG hG₀ hδ C hC m _
  square_integrable := fun _ => Integrable.of_finite
  mean := fun q => by
    rw [integral_sub Integrable.of_finite (integrable_const _),
      sampleGradient_mean hG hG₀ hδ m _ (BernoulliOracle.probability_pos hB)]
    simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_self]
  variance := sampleGradient_variance_bound hG hG₀ hδ hm hB hdiff henv C

variable {m η B σ : ℝ} (hm : 0≤m) (hB : 0<B)
  (hdiff : ∀ v,‖G v-G₀ v‖≤η) (henv : (Real.sqrt 2*m/(1-(δ:ℝ)))*η≤B)
  {Past : Type*} [MeasurableSpace Past] {ν : Measure Past} [IsProbabilityMeasure ν]
include hm hdiff henv

theorem adaptive_variance (q : Past → Joint X Y) (hq : Measurable q) :
    (∫ z,‖sampleGradient hG hG₀ hδ m (BernoulliOracle.probability B σ) C z.2 (q z.1)-
      meanGradient hG hδ m C (q z.1)‖^2 ∂ν.prod
        (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)))≤σ^2 :=
  (freshOracle hG hG₀ hδ C hC hm hB hdiff henv).adaptiveError_variance q hq

theorem adaptive_centering (q : Past → Joint X Y) (hq : Measurable q)
    (s : Set (Past × Bool))
    (hs : MeasurableSet[FreshOracle.Oracle.pastSpace] s) :
    (∫ z in s,sampleGradient hG hG₀ hδ m (BernoulliOracle.probability B σ) C z.2 (q z.1)-
      meanGradient hG hδ m C (q z.1) ∂ν.prod
        (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)))=0 :=
  (freshOracle hG hG₀ hδ C hC hm hB hdiff henv).adaptiveError_setIntegral q hq s hs

end Bilevel.PartialLegendre.ConjugateOracle
