import HeavyTail.GaussianMixtureEntropy
import HeavyTail.GaussianTranslation

/-!
# Gaussian mixture entropy plus quadratic mirror optimizers

All entropy derivatives and integrability facts are discharged for actual finite
Gaussian mixtures. The compact simplex gives exact optimizer existence. The
theorems about realized updates are pathwise; no measurability of a chosen
optimizer is asserted here.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The quadratic penalty on a linear mixture mean is convex. -/
theorem meanPenalty_convex {S : Set (ι → ℝ)} (hS : Convex ℝ S)
    {β : ℝ} (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) :
    ConvexOn ℝ S (fun w => β / 2 * ‖M w‖ ^ 2) := by
  refine ⟨hS, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hid : ‖M (a • x + b • y)‖ ^ 2 =
      a * ‖M x‖ ^ 2 + b * ‖M y‖ ^ 2 - a * b * ‖M x - M y‖ ^ 2 := by
    have hb' : b = 1 - a := by linarith
    subst b
    simp only [map_add, map_smul, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right, norm_sub_sq_real]
    ring
  have hnonneg : 0 ≤ β / 2 * (a * b * ‖M x - M y‖ ^ 2) := by positivity
  simp only [smul_eq_mul]
  rw [hid]
  nlinarith

namespace GaussianEntropy

open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The exponential density is exactly the translated Gaussian law. -/
theorem gaussianExponentialDensity_measure (t : E) :
    densityMeasure (euclideanGaussianLaw E) (gaussianExponentialDensity E t) =
      (euclideanGaussianLaw E).map (fun z => t + z) := by
  simpa only [densityMeasure, gaussianExponentialDensity, gaussianLogDensity,
    GaussianLower.exponentialRatio] using GaussianLower.euclideanGaussian_translation E t

abbrev gaussianMixtureGenerator (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) : (ι → ℝ) → ℝ :=
  meanRegularizedEntropy (euclideanGaussianLaw E)
    (fun i => gaussianExponentialDensity E (t i)) β M

abbrev gaussianMixtureGeneratorDerivative (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ :=
  meanRegularizedEntropyDerivative (euclideanGaussianLaw E)
    (fun i => gaussianExponentialDensity E (t i)) β M

theorem gaussian_mixture_generator_derivative (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    HasFDerivWithinAt (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M w) (stdSimplex ℝ ι) w :=
  (gaussian_mixture_entropy_derivative E t hw).add
    (meanPenalty_derivative β M w).hasFDerivWithinAt

theorem gaussian_mixture_generator_continuous (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) :
    ContinuousOn (gaussianMixtureGenerator E t β M) (stdSimplex ℝ ι) :=
  fun _w hw => (gaussian_mixture_generator_derivative E t β M hw).continuousWithinAt

theorem gaussian_mixture_generator_convex (t : ι → E) {β : ℝ}
    (hβ : 0 ≤ β) (M : (ι → ℝ) →L[ℝ] V) :
    ConvexOn ℝ (stdSimplex ℝ ι) (gaussianMixtureGenerator E t β M) :=
  (mixtureEntropy_convex (fun _i _z => Real.exp_pos _)
    (fun _w hw => (gaussian_mixture_entropy_regular E t hw).1)).add
      (meanPenalty_convex (convex_stdSimplex ℝ ι) hβ M)

theorem gaussian_mixture_generator_bregman (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) {q p : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι) :
    bregmanDivergence (gaussianMixtureGenerator E t β M)
      (gaussianMixtureGeneratorDerivative E t β M) q p =
      densityRelativeEntropy (euclideanGaussianLaw E)
        (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) q)
        (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) p) +
          β / 2 * ‖M q - M p‖ ^ 2 :=
  meanRegularizedEntropy_bregman_eq_KL (fun _i _z => Real.exp_pos _)
    (fun i => gaussianExponentialDensity_integrable E (t i))
    (fun i => gaussianExponentialDensity_normalized E (t i)) hq hp
    (gaussian_mixture_entropy_regular E t hq).1
    (gaussian_mixture_entropy_regular E t hp).1
    (gaussian_mixture_entropy_regular E t hp).2 β M

/-- Exact optimizer existence, without claiming a measurable selection. -/
theorem gaussian_mixture_quadratic_optimizer_exists [Nonempty ι]
    (t : ι → E) (β : ℝ) (M : (ι → ℝ) →L[ℝ] V)
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    ∃ y ∈ stdSimplex ℝ ι, IsMinOn
      (fun z => L z + bregmanDivergence (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) z x) (stdSimplex ℝ ι) y := by
  classical
  apply (isCompact_stdSimplex ι).exists_isMinOn
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  · intro w hw
    exact (mirror_objective_derivative L
      (gaussian_mixture_generator_derivative E t β M hw)).continuousWithinAt

/-- The genuine Gaussian entropy optimizer obeys the Bregman update inequality. -/
theorem gaussian_mixture_mirror_update (t : ι → E) (β : ℝ)
    (M : (ι → ℝ) →L[ℝ] V) (L : (ι → ℝ) →L[ℝ] ℝ) {x y q : ι → ℝ}
    (hy : y ∈ stdSimplex ℝ ι) (hq : q ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn
      (fun z => L z + bregmanDivergence (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) z x) (stdSimplex ℝ ι) y) :
    bregmanDivergence (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) q y ≤
      bregmanDivergence (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) q x + L q +
      mirrorStability (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) L x y :=
  mirror_update_inequality L (convex_stdSimplex ℝ ι) hy hq
    (gaussian_mixture_generator_derivative E t β M hy) hmin

/-- Pathwise finite regret from exact realized minimizers, with actual KL initial cost. -/
theorem gaussian_mixture_pathwise_regret (t : ι → E) {β : ℝ} (hβ : 0 ≤ β)
    (M : (ι → ℝ) →L[ℝ] V) {x : ℕ → (ι → ℝ)}
    {L : ℕ → (ι → ℝ) →L[ℝ] ℝ} {q : ι → ℝ}
    (hx : ∀ k, x k ∈ stdSimplex ℝ ι) (hq : q ∈ stdSimplex ℝ ι)
    (hmin : ∀ k, IsMinOn
      (fun z => L k z + bregmanDivergence (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) z (x k))
      (stdSimplex ℝ ι) (x (k + 1))) (n : ℕ) :
    -(∑ k ∈ Finset.range n, L k q) ≤
      densityRelativeEntropy (euclideanGaussianLaw E)
        (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) q)
        (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) (x 0)) +
      β / 2 * ‖M q - M (x 0)‖ ^ 2 +
      ∑ k ∈ Finset.range n, mirrorStability (gaussianMixtureGenerator E t β M)
        (gaussianMixtureGeneratorDerivative E t β M) (L k) (x k) (x (k + 1)) := by
  have h := mirror_descent_regret (gaussian_mixture_generator_convex E t hβ M) hx hq
    (fun w hw => gaussian_mixture_generator_derivative E t β M hw) hmin n
  rwa [gaussian_mixture_generator_bregman E t β M hq (hx 0)] at h

end GaussianEntropy
end HeavyTail
