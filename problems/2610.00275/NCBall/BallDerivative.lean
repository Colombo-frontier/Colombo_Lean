import NCBall.BallSmoothing
import NCBall.SmoothingGoldstein
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating ball smoothing of a Lipschitz function -/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology NNReal
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (τ : Measure E) [τ.IsAddHaarMeasure] (ρ : ℝ) (hρ : 0 < ρ)

theorem ballLaw_ae_differentiable {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    ∀ᵐ z ∂ballLaw τ ρ hρ, DifferentiableAt ℝ f (x + z) :=
  (ballLaw_absolutelyContinuous τ ρ hρ).ae_le
    ((eventually_add_left_iff τ x).2 (hf.ae_differentiableAt (μ := τ)))

theorem ballAverage_hasFDerivAt {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    HasFDerivAt (ballAverage τ ρ hρ f) (∫ z, fderiv ℝ f (x + z) ∂ballLaw τ ρ hρ) x := by
  have hm : AEStronglyMeasurable (fun z => fderiv ℝ f (x + z)) (ballLaw τ ρ hρ) :=
    ((measurable_fderiv ℝ f).comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hdiff : ∀ᵐ z ∂ballLaw τ ρ hρ,
      HasFDerivAt (fun y => f (y + z)) (fderiv ℝ f (x + z)) x := by
    filter_upwards [ballLaw_ae_differentiable τ ρ hρ hf x] with z hz
    simpa only [ContinuousLinearMap.comp_id] using hz.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const z)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip (μ := ballLaw τ ρ hρ)
    (F := fun y z => f (y + z)) (F' := fun z => fderiv ℝ f (x + z)) (bound := fun _ => (L : ℝ))
    (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall (fun y => (hf.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable))
    (ballTranslate_integrable τ ρ hρ hf x) hm
    (Eventually.of_forall (fun z => by
      simpa only [Real.nnabs_of_nonneg L.coe_nonneg, Real.toNNReal_coe, mul_one, Function.comp_def] using
        (hf.comp (isometry_add_right z).lipschitz).lipschitzOnWith))
    (integrable_const _) hdiff).2

theorem measurable_gradient (f : E → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_gradient_le_of_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    ‖gradient f x‖ ≤ L := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)

theorem ball_gradient_integrable {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    Integrable (fun z => gradient f (x + z)) (ballLaw τ ρ hρ) := by
  apply (integrable_const (L : ℝ)).mono'
    ((measurable_gradient f).comp (measurable_const.add measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun z => norm_gradient_le_of_lipschitz hf (x + z))

theorem ballAverage_gradient {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    gradient (ballAverage τ ρ hρ f) x = ∫ z, gradient f (x + z) ∂ballLaw τ ρ hρ := by
  have hi : Integrable (fun z => fderiv ℝ f (x + z)) (ballLaw τ ρ hρ) := by
    apply (integrable_const (L : ℝ)).mono'
      ((measurable_fderiv ℝ f).comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact Eventually.of_forall (fun z => norm_fderiv_le_of_lipschitz ℝ hf)
  rw [(ballAverage_hasFDerivAt τ ρ hρ hf x).hasGradientAt.gradient]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi).symm

theorem ballAverage_gradient_mem {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    gradient (ballAverage τ ρ hρ f) x ∈ clarkeGoldsteinSet f ρ x := by
  rw [ballAverage_gradient τ ρ hρ hf x]
  exact integral_gradient_mem_clarkeGoldstein f (fun z => x + z) x ρ
    (ballLaw_shift_mem τ ρ hρ x) (ballLaw_ae_differentiable τ ρ hρ hf x)
    (ball_gradient_integrable τ ρ hρ hf x)

end NCBall
