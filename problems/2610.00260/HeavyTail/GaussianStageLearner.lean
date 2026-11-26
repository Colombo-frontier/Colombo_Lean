import HeavyTail.GaussianOnlineInitialization
import HeavyTail.CompositeStagePolicy

/-! Public concrete finite-Gaussian learner for the actual capped oracle
policy. Its selection and state depend on public data and observed replies. -/

noncomputable section
open MeasureTheory Set

namespace HeavyTail.GaussianEntropy

universe u
variable {ι E : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianStageLearner (c : E) (R a η β : ℝ) (centers : ι → E)
    (hc : ∀ i, ‖centers i - c‖ ≤ R) (initial : SimplexPoint ι)
    {ε : ℝ} (hε : 0 < ε) : StageLearner (SimplexPoint ι) E c R where
  initial := initial
  point w := finiteMixtureMean centers w.val
  point_measurable := (finiteMixtureMean centers).continuous.measurable.comp measurable_subtype_coe
  point_bound w := finiteMixtureMean_ball E c R centers hc w.property
  update := gaussianOnlineUpdate E c a η β centers hε
  update_measurable := gaussianOnlineUpdate_measurable E c a η β centers hε

end HeavyTail.GaussianEntropy
