import Bilevel.MultiscaleOracle
import Bilevel.CompensatedMeanJointHessian
import Bilevel.FreshOracle

/-! The actual multiscale oracle as a measurable fresh-sample oracle. Fubini
then gives variance and conditional centering at arbitrary measurable queries
chosen from the whole past. -/

noncomputable section
namespace Bilevel.MultiscaleMean.Parameters
open CompensatedMean MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} (P : Parameters (E := E) n)

theorem lowerY_joint_continuous : Continuous (fun z : E × LowerSpace E => P.data.lowerY z.1 z.2) :=
  continuous_iff_continuousAt.mpr (fun z => (P.data.lowerY_joint_hasFDerivAt z).continuousAt)

theorem signalY_continuous : Continuous P.signalY := by
  have he : P.signalY = gradient P.signal := funext (fun y => (P.signal_hasGradientAt y).gradient.symm)
  rw [he]
  exact (GradientJetBounds.gradient_contDiff P.signal_contDiff).continuous

theorem inactiveLowerY_joint_continuous :
    Continuous (fun z : E × LowerSpace E => P.inactiveLowerY z.1 z.2) :=
  P.lowerY_joint_continuous.sub (P.signalY_continuous.comp continuous_snd)

variable [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [SecondCountableTopology (LowerSpace E)]

theorem sampleLowerY_measurable (p : ℝ) :
    Measurable (fun qb : (E × LowerSpace E) × Bool => P.sampleLowerY p qb.1.1 qb.1.2 qb.2) := by
  have hi : Measurable (fun qb : (E × LowerSpace E) × Bool => P.inactiveLowerY qb.1.1 qb.1.2) :=
    P.inactiveLowerY_joint_continuous.measurable.comp measurable_fst
  have hs : Measurable (fun qb : (E × LowerSpace E) × Bool => P.signalY qb.1.2) :=
    P.signalY_continuous.measurable.comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun qb : (E × LowerSpace E) × Bool => if qb.2 then p⁻¹ else (0:ℝ)) :=
    (measurable_of_finite (fun b : Bool => if b then p⁻¹ else (0:ℝ))).comp measurable_snd
  exact hi.add (hc.smul hs)

def freshOracle (σ : ℝ) (hscale : P.β*P.θ ≤ 1) :
    FreshOracle.Oracle (Query := E × LowerSpace E) (E := LowerSpace E)
      (BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) σ where
  truth := fun q => P.data.lowerY q.1 q.2
  sample := fun q b => P.sampleLowerY (P.activationProbability σ) q.1 q.2 b
  truth_measurable := P.lowerY_joint_continuous.measurable
  sample_measurable := P.sampleLowerY_measurable _
  square_integrable := fun _ => Integrable.of_finite
  mean := fun q => by
    rw [integral_sub Integrable.of_finite (integrable_const _),
      P.sampleLowerY_mean _ q.1 q.2 (P.activationProbability_pos σ) (P.activationProbability_le_one σ)]
    simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_self]
  variance := fun q => P.sampleLowerY_variance σ q.1 q.2 hscale

variable {Past : Type*} [MeasurableSpace Past] (ν : Measure Past) [IsProbabilityMeasure ν]

theorem adaptive_variance (σ : ℝ) (hscale : P.β*P.θ ≤ 1)
    (q : Past → E × LowerSpace E) (hq : Measurable q) :
    (∫ zb,‖P.sampleLowerY (P.activationProbability σ) (q zb.1).1 (q zb.1).2 zb.2-
      P.data.lowerY (q zb.1).1 (q zb.1).2‖^2
      ∂ν.prod (BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ))) ≤ σ^2 :=
  (P.freshOracle σ hscale).adaptiveError_variance (μ := ν) q hq

theorem adaptive_conditional_centering (σ : ℝ) (hscale : P.β*P.θ ≤ 1)
    (q : Past → E × LowerSpace E) (hq : Measurable q) :
    (condExpL2 (LowerSpace E) ℝ (FreshOracle.Oracle.pastSpace_le (Past := Past) (Seed := Bool))
      ((P.freshOracle σ hscale).adaptiveErrorLp (μ := ν) q hq) :
      Lp (LowerSpace E) 2 (ν.prod (BernoulliOracle.law (P.activationProbability σ)
        (P.activationProbability_le_one σ)))) = 0 :=
  (P.freshOracle σ hscale).adaptiveErrorLp_condExpL2 (μ := ν) q hq

end Bilevel.MultiscaleMean.Parameters
