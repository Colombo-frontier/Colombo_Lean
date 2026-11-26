import HeavyTail.GaussianMeasurableUpdateLoss
import HeavyTail.GaussianOnlineStabilityVariational

/-! Actual Gaussian cross entropy and exponential integral facts needed by
the online stability calculation. Integrability is derived from the finite
Gaussian envelopes and Gaussian moment-generating functions. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem mixture_cross_log_integrable {μ : Measure Ω} {φ : ι → Ω → ℝ}
    (hφint : ∀ i, Integrable (φ i) μ) (q p : ι → ℝ)
    (hdint : Integrable (mixtureEntropyDifferential φ p) μ) :
    Integrable (fun ω => mixtureDensity φ q ω * Real.log (mixtureDensity φ p ω)) μ := by
  have heq : (fun ω => mixtureDensity φ q ω * Real.log (mixtureDensity φ p ω)) =
      (fun ω => mixtureEntropyDifferential φ p ω q - mixtureDensity φ q ω) := by
    funext ω
    simp only [mixtureEntropyDifferential, ContinuousLinearMap.smul_apply, smul_eq_mul,
      mixtureDensity]
    ring
  rw [heq]
  exact (hdint.apply_continuousLinearMap q).sub (mixtureDensity_integrable hφint q)

theorem mixture_relative_entropy_integrable {μ : Measure Ω} {φ : ι → Ω → ℝ}
    (hφpos : ∀ i ω, 0 < φ i ω) (hφint : ∀ i, Integrable (φ i) μ)
    {q p : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hqent : Integrable (mixtureEntropyIntegrand φ q) μ)
    (hdint : Integrable (mixtureEntropyDifferential φ p) μ) :
    Integrable (fun ω => mixtureDensity φ q ω *
      Real.log (mixtureDensity φ q ω / mixtureDensity φ p ω)) μ := by
  have heq : (fun ω => mixtureDensity φ q ω * Real.log (mixtureDensity φ q ω / mixtureDensity φ p ω)) =
      (fun ω => mixtureEntropyIntegrand φ q ω - mixtureDensity φ q ω * Real.log (mixtureDensity φ p ω)) := by
    funext ω
    rw [Real.log_div (mixtureDensity_pos hφpos hq ω).ne' (mixtureDensity_pos hφpos hp ω).ne']
    simp only [mixtureEntropyIntegrand, mul_sub]
  rw [heq]
  exact hqent.sub (mixture_cross_log_integrable hφint q p hdint)

namespace GaussianEntropy
open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_mixture_relative_entropy_integrable (t : ι → E)
    {q p : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι) :
    Integrable (fun z => mixtureDensity (fun i => gaussianExponentialDensity E (t i)) q z *
      Real.log (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) q z /
        mixtureDensity (fun i => gaussianExponentialDensity E (t i)) p z)) (euclideanGaussianLaw E) :=
  mixture_relative_entropy_integrable (fun _i _z => Real.exp_pos _)
    (fun i => gaussianExponentialDensity_integrable E (t i)) hq hp
    (gaussian_mixture_entropy_regular E t hq).1 (gaussian_mixture_entropy_regular E t hp).2

theorem gaussian_affine_exp_integral (v : E) (k : ℝ) :
    (∫ z, Real.exp (⟪v, z⟫_ℝ + k) ∂euclideanGaussianLaw E) = Real.exp (k + ‖v‖ ^ 2 / 2) := by
  simp only [Real.exp_add, integral_mul_const, gaussian_exp_inner]
  ring

theorem gaussian_weighted_affine_exp_integrable (t v : E) (k : ℝ) :
    Integrable (fun z => gaussianExponentialDensity E t z * Real.exp (⟪v, z⟫_ℝ + k))
      (euclideanGaussianLaw E) := by
  convert gaussian_affine_exp_integrable E (t + v) (k - ‖t‖ ^ 2 / 2) using 1
  funext z
  simp only [gaussianExponentialDensity, ← Real.exp_add, gaussianLogDensity, inner_add_left]
  congr 1
  ring

theorem gaussian_weighted_affine_exp_integral (t v : E) (k : ℝ) :
    (∫ z, gaussianExponentialDensity E t z * Real.exp (⟪v, z⟫_ℝ + k) ∂euclideanGaussianLaw E) =
      Real.exp (k + ⟪v, t⟫_ℝ + ‖v‖ ^ 2 / 2) := by
  rw [← integral_densityMeasure (w := gaussianExponentialDensity E t)
    (gaussianLogDensity_measurable E t).exp (fun _ => (Real.exp_pos _).le)
      (fun z => Real.exp (⟪v, z⟫_ℝ + k)), gaussianExponentialDensity_measure,
    integral_map (f := fun z => Real.exp (⟪v, z⟫_ℝ + k))
      (show Measurable (fun z : E => t + z) by fun_prop).aemeasurable
      (show Measurable (fun z : E => Real.exp (⟪v, z⟫_ℝ + k)) by fun_prop).aestronglyMeasurable]
  have heq : (fun z : E => Real.exp (⟪v, t + z⟫_ℝ + k)) =
      (fun z => Real.exp (⟪v, z⟫_ℝ + (k + ⟪v, t⟫_ℝ))) := by
    funext z
    rw [inner_add_right]
    congr 1
    ring
  rw [heq, gaussian_affine_exp_integral]

end GaussianEntropy
end HeavyTail
