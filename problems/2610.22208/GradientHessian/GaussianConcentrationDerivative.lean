import GradientHessian.GaussianConcentrationSemigroup
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Differentiation of the actual Mehler integral.  For continuously
differentiable Lipschitz functions, the spatial derivative commutes with
Gaussian smoothing, with the exact contraction factor. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Filter
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem lipschitz_affine_integrable {b : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith b f) (a : ℝ) (c : E) :
    Integrable (fun z => f (c + a • z)) (euclideanGaussianLaw E) := by
  have hl : LipschitzWith ‖a‖₊ (fun z : E => c + a • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, coe_nnnorm]
    exact le_rfl
  exact lipschitz_integrable (hf.comp hl)

theorem mehler_hasFDerivAt {b : ℝ≥0} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith b f) (ρ : ℝ) (x : E) :
    HasFDerivAt (mehler E ρ f)
      (ρ • ∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
        ∂euclideanGaussianLaw E) x := by
  let σ := Real.sqrt (1 - ρ ^ 2)
  let F : E → E → ℝ := fun y z => f (ρ • y + σ • z)
  let F' : E → E → E →L[ℝ] ℝ := fun y z => ρ • fderiv ℝ f (ρ • y + σ • z)
  have hdiff (y z : E) : HasFDerivAt (fun w => F w z) (F' y z) y := by
    have hi := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul ρ).add_const (σ • z)
    have ho := (hf.differentiable (by norm_num) (ρ • y + σ • z)).hasFDerivAt.comp y hi
    convert ho using 1
    ext u
    simp only [F', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul]
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (euclideanGaussianLaw E) := by
    apply Eventually.of_forall
    intro y
    exact (hf.continuous.comp ((continuous_const.add (continuous_const.smul continuous_id)))).aestronglyMeasurable
  have h'int : Integrable (F x) (euclideanGaussianLaw E) :=
    lipschitz_affine_integrable hLip σ (ρ • x)
  have h'dmeas : AEStronglyMeasurable (F' x) (euclideanGaussianLaw E) := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.smul ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_const.smul continuous_id)))
  have hbnd : ∀ᵐ z ∂euclideanGaussianLaw E, ∀ y ∈ Metric.ball x 1,
      ‖F' y z‖ ≤ ‖ρ‖ * (b : ℝ) := by
    apply ae_of_all
    intro z y _
    dsimp [F']
    calc
      ‖ρ • fderiv ℝ f (ρ • y + σ • z)‖ =
          ‖ρ‖ * ‖fderiv ℝ f (ρ • y + σ • z)‖ :=
            norm_smul ρ (fderiv ℝ f (ρ • y + σ • z))
      _ ≤ ‖ρ‖ * (b : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg ρ)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := euclideanGaussianLaw E)
    (F := F) (F' := F') (bound := fun _ => ‖ρ‖ * (b : ℝ))
    (by norm_num : (0 : ℝ) < 1) hmeas h'int h'dmeas hbnd (integrable_const _)
    (ae_of_all _ fun z y _ => hdiff y z)
  dsimp [F'] at hd
  rw [integral_smul] at hd
  exact hd

theorem mehler_fderiv {b : ℝ≥0} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith b f) (ρ : ℝ) (x : E) :
    fderiv ℝ (mehler E ρ f) x =
      ρ • ∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
        ∂euclideanGaussianLaw E := (mehler_hasFDerivAt hf hLip ρ x).fderiv

theorem ornsteinUhlenbeck_fderiv {b : ℝ≥0} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith b f) (t : ℝ) (x : E) :
    fderiv ℝ (ornsteinUhlenbeck E t f) x =
      Real.exp (-t) • ∫ z,
        fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - (Real.exp (-t)) ^ 2) • z)
          ∂euclideanGaussianLaw E := mehler_fderiv hf hLip _ x

end GradientHessian.GaussianConcentration
