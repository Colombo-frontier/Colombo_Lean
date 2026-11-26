import HeavyTail.GaussianTranslatedLearner
import HeavyTail.CappedParameterizedRule

/-! The public Gaussian stage as a jointly measurable policy in its initial
feasible center. Its update is chosen once at center zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace HeavyTail
universe u
variable {ι E : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters}

structure GaussianStageConfig (ι E : Type u) [Fintype ι] [NormedAddCommGroup E] (R : ℝ) where
  a : ℝ
  eta : ℝ
  beta : ℝ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  offsets : ι → E
  offsets_bound : ∀ i, ‖offsets i‖ ≤ R
  initial : SimplexPoint ι

def GaussianStageConfig.learner {R : ℝ} (C : GaussianStageConfig ι E R) (c : E) :
    StageLearner (SimplexPoint ι) E c R :=
  GaussianEntropy.translatedGaussianStageLearner c C.a C.eta C.beta C.offsets
    C.offsets_bound C.initial C.epsilon_pos

theorem GaussianStageConfig.learner_point {R : ℝ} (C : GaussianStageConfig ι E R)
    (c : E) (w : SimplexPoint ι) :
    (C.learner c).point w = finiteMixtureMean (fun i => c + C.offsets i) w.val :=
  (GaussianEntropy.finiteMixtureMean_translate c C.offsets w.property).symm

theorem GaussianStageConfig.learner_first_order {R : ℝ} (C : GaussianStageConfig ι E R)
    (c : E) (w : SimplexPoint ι) (Y : E) (q : SimplexPoint ι) :
    -C.epsilon ≤ (GaussianEntropy.observedClippedLoss E c C.a C.eta
        (fun i => c + C.offsets i) (Y, w.val) +
      GaussianEntropy.gaussianOnlineDerivative E c C.a C.beta (fun i => c + C.offsets i)
        ((C.learner c).update (w, Y)).val -
      GaussianEntropy.gaussianOnlineDerivative E c C.a C.beta (fun i => c + C.offsets i) w.val)
        (q.val - ((C.learner c).update (w, Y)).val) :=
  GaussianEntropy.translatedGaussianUpdate_first_order c C.a C.eta C.beta C.offsets
    C.epsilon_pos Y w q.property

namespace PublicProblem
variable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
  (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (C : GaussianStageConfig ι E R)

def gaussianCenterRule (c : B.X) :
    CappedRaw.Rule (CompositeStageState (SimplexPoint ι) E) B.X E B.X :=
  B.stageRule hR hn τ (C.learner c)

theorem gaussianCenterPoint_measurable :
    Measurable (fun z : B.X × CompositeStageState (SimplexPoint ι) E =>
      (C.learner z.1).point z.2.1) := by
  exact (GaussianEntropy.translatedGaussianPoint_measurable C.offsets).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))

theorem gaussianCenterQuery_measurable :
    Measurable (fun z : B.X × CompositeStageState (SimplexPoint ι) E =>
      (B.gaussianCenterRule hR hn τ C z.1).query z.2) :=
  (B.stageQuery_measurable hR hn).comp (B.gaussianCenterPoint_measurable C)

theorem gaussianCenterAcceptance_measurable :
    MeasurableSet {z : B.X × (CompositeStageState (SimplexPoint ι) E × E) |
      z.2 ∈ (B.gaussianCenterRule hR hn τ C z.1).acceptance} := by
  have hp : Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) =>
      (C.learner z.1).point z.2.1.1) :=
    (B.gaussianCenterPoint_measurable C).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact (B.stageAcceptance_measurable hR hn τ).preimage
    (hp.prodMk (measurable_snd.comp measurable_snd))

theorem gaussianCenterUpdate_measurable :
    Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) =>
      (B.gaussianCenterRule hR hn τ C z.1).update z.2) := by
  have hw : Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) => z.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hp : Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) =>
      (C.learner z.1).point z.2.1.1) :=
    (B.gaussianCenterPoint_measurable C).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hg := B.correctedReply_measurable hR hn |>.comp
    (hp.prodMk (measurable_snd.comp measurable_snd))
  have hs : Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) => z.2.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hk : Measurable (fun z : B.X × (CompositeStageState (SimplexPoint ι) E × E) => z.2.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact ((GaussianEntropy.gaussianOnlineUpdate_measurable E 0 C.a C.eta C.beta C.offsets
    C.epsilon_pos).comp (hw.prodMk hg)).prodMk
      ((hs.add ((selectedProximalPoint_measurable B.prox B.h_convex θ.G_pos hR hn).comp hp)).prodMk
        (hk.add_const 1))

theorem gaussianCenterReadout_measurable :
    Measurable (fun z : B.X × CompositeStageState (SimplexPoint ι) E =>
      (B.gaussianCenterRule hR hn τ C z.1).readout z.2) :=
  (B.stageReadout_measurable n).comp measurable_snd

def gaussianCenteredRule :
    CappedRaw.Rule (B.X × CompositeStageState (SimplexPoint ι) E) B.X E B.X :=
  CappedRaw.parameterizedRule (B.gaussianCenterRule hR hn τ C)
    (B.gaussianCenterQuery_measurable hR hn τ C)
    (B.gaussianCenterAcceptance_measurable hR hn τ C)
    (B.gaussianCenterUpdate_measurable hR hn τ C)
    (B.gaussianCenterReadout_measurable hR hn τ C)

def gaussianCenteredStagePolicy (T : ℕ) : AdaptiveKernel.Policy B.X B.X E B.X T :=
  (B.gaussianCenteredRule hR hn τ C).policy
    (fun c => (c, (C.initial, (0, 0))))
    (measurable_id.prodMk measurable_const) n T

theorem gaussianCenteredStagePolicy_outputLaw_dirac (c : B.X) (T : ℕ)
    (K : Kernel B.X E) [IsMarkovKernel K] :
    (B.gaussianCenteredStagePolicy hR hn τ C T).outputLaw (Measure.dirac c) K =
      (B.cappedStagePolicy hR hn τ (C.learner c) T).outputLaw
        (Measure.dirac PUnit.unit) K :=
  CappedRaw.parameterizedRule_outputLaw_dirac (B.gaussianCenterRule hR hn τ C)
    (B.gaussianCenterQuery_measurable hR hn τ C)
    (B.gaussianCenterAcceptance_measurable hR hn τ C)
    (B.gaussianCenterUpdate_measurable hR hn τ C)
    (B.gaussianCenterReadout_measurable hR hn τ C)
    (fun _ : B.X => (C.initial, (0, 0))) measurable_const c n T K

end PublicProblem
end HeavyTail
