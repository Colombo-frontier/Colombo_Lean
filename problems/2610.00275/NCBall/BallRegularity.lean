import NCBall.BallDerivative
import NCBall.BallAverageContinuity

/-! # Actual ball smoothing is C¹ and transfers Goldstein stationarity

All averaging identities and regularity hypotheses are discharged for a
globally Lipschitz function, using Haar measure on a positive-radius ball.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (τ : Measure E) [τ.IsAddHaarMeasure] (ρ : ℝ) (hρ : 0 < ρ)

theorem ballAverage_contDiff {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContDiff ℝ 1 (ballAverage τ ρ hρ f) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨ballAverage τ ρ hρ (fderiv ℝ f), ?_, ballAverage_hasFDerivAt τ ρ hρ hf⟩
  exact ballAverage_continuous_of_bounded τ ρ hρ (fderiv ℝ f) (measurable_fderiv ℝ f)
    L.coe_nonneg (fun _ => norm_fderiv_le_of_lipschitz ℝ hf)

theorem ballAverage_gradient_continuous {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Continuous (gradient (ballAverage τ ρ hρ f)) :=
  gradient_continuous_of_C1 (ballAverage_contDiff τ ρ hρ hf)

theorem ballAverage_clarke_subset {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (ν : ℝ) (x : E) :
    clarkeGoldsteinSet (ballAverage τ ρ hρ f) ν x ⊆ clarkeGoldsteinSet f (ρ + ν) x :=
  averaged_gradient_clarke_subset f (ballAverage τ ρ hρ f) (ballAverage_contDiff τ ρ hρ hf)
    (fun y z => y + z) x (ballLaw_shift_mem τ ρ hρ)
    (ballLaw_ae_differentiable τ ρ hρ hf) (ball_gradient_integrable τ ρ hρ hf)
    (ballAverage_gradient τ ρ hρ hf)

theorem ballAverage_residual_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ν : ℝ} (hν : 0 ≤ ν) (x : E) :
    clarkeGoldsteinResidual f (ρ + ν) x ≤
      clarkeGoldsteinResidual (ballAverage τ ρ hρ f) ν x :=
  averaged_gradient_residual_bound f (ballAverage τ ρ hρ f) (ballAverage_contDiff τ ρ hρ hf)
    (fun y z => y + z) hν x (ballLaw_shift_mem τ ρ hρ)
    (ballLaw_ae_differentiable τ ρ hρ hf) (ball_gradient_integrable τ ρ hρ hf)
    (ballAverage_gradient τ ρ hρ hf)

end NCBall
