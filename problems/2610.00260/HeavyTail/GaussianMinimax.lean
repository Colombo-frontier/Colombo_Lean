import HeavyTail.GaussianAdaptiveMoments
import HeavyTail.AdaptiveKernelRandomized
import HeavyTail.MinimaxQuantile

/-! The calibrated Gaussian trace lower bound as an actual family minimax
quantile over all measurable adaptive policies with arbitrary seed laws. -/

open MeasureTheory
open scoped ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

def traceRate (μ D G L : ℝ) (T : ℕ) : ℝ :=
  (1 / 16384 : ℝ) * envelope μ D (min G (L / Real.sqrt T))

def traceExperimentLaw {k T : ℕ} (μ D a L : ℝ) (v : Fin k → Bool)
    (A : AdaptiveKernel.RandomizedPolicy (HardSpace k) (HardSpace k) (HardSpace k) T) :
    Measure (AdaptiveKernel.History A.Seed (HardSpace k) T) :=
  A.strategy.historyLaw A.seedLaw
    (traceKernel a (envelopeRadius μ D a / Real.sqrt k) (L / Real.sqrt k) v) T

instance traceExperimentLaw_probability {k T : ℕ} (μ D a L : ℝ) (v : Fin k → Bool)
    (A : AdaptiveKernel.RandomizedPolicy (HardSpace k) (HardSpace k) (HardSpace k) T) :
    IsProbabilityMeasure (traceExperimentLaw μ D a L v A) := by
  unfold traceExperimentLaw
  infer_instance

def traceExperimentLoss {k T : ℕ} (μ D a : ℝ) (v : Fin k → Bool)
    (A : AdaptiveKernel.RandomizedPolicy (HardSpace k) (HardSpace k) (HardSpace k) T)
    (h : AdaptiveKernel.History A.Seed (HardSpace k) T) : ℝ :=
  traceLoss μ D a v (A.strategy.output h)

def traceFamilyQuantile (k T : ℕ) (μ D a L δ : ℝ) : ℝ≥0∞ :=
  minimaxErrorQuantile (traceExperimentLaw (k := k) (T := T) μ D a L)
    (traceExperimentLoss μ D a) δ

theorem gaussian_trace_rate_probability_lower {k T : ℕ} (hk : 0 < k) (hT : 0 < T)
    {μ D G L δ : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hL : 0 < L)
    (hδ : δ < 1 / 4)
    (A : AdaptiveKernel.RandomizedPolicy (HardSpace k) (HardSpace k) (HardSpace k) T) :
    ∃ v : Fin k → Bool, δ <
      (traceExperimentLaw μ D (traceAmplitude G L T) L v A).real
        {h | traceRate μ D G L T ≤ traceExperimentLoss μ D (traceAmplitude G L T) v A h} := by
  have ha := traceAmplitude_nonneg hG hL.le T
  obtain ⟨v, hv⟩ := gaussian_objective_probability_lower hk A.strategy A.seedLaw
    hμ hD ha hL (traceAmplitude_testing hG hL hT)
  refine ⟨v, hδ.trans_le (hv.trans (measureReal_mono ?_))⟩
  intro h hh
  exact (traceAmplitude_envelope hμ hD hG hL.le T).trans hh

/-- The Gaussian trace component `eq:lb-trace`, for the concrete admissible family. -/
theorem traceFamilyQuantile_lower {k T : ℕ} (hk : 0 < k) (hT : 0 < T)
    {μ D G L δ : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hL : 0 < L)
    (hδ : δ < 1 / 4) :
    ENNReal.ofReal (traceRate μ D G L T) ≤
      traceFamilyQuantile k T μ D (traceAmplitude G L T) L δ := by
  apply minimaxErrorQuantile_lower
  exact gaussian_trace_rate_probability_lower hk hT hμ hD hG hL hδ

end
end HeavyTail.GaussianLower
