import HeavyTail.GaussianOnlineStabilityExp

/-! The actual Gaussian-mixture mirror stability bound. The entropy
variational inequality, Gaussian integrability and mean-square completion
are all proved dependencies; the stability conclusion is not a premise. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_online_error_variational (c : E) (a η : ℝ) (centers : ι → E)
    {q p : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (Y b x : E) :
    -(∫ u, onlineMixtureError E η Y b x u ∂physicalGaussianMixtureLaw E c a centers q) -
      densityRelativeEntropy (euclideanGaussianLaw E)
        (physicalMixtureDensity E c a centers q) (physicalMixtureDensity E c a centers p) ≤
      Real.log (onlineMixtureW E c a η centers p Y b x) := by
  let g : E → ℝ := fun z => -onlineMixtureError E η Y b x (c + a • z)
  have hnegmeas : Measurable (fun u => -onlineMixtureError E η Y b x u) := by
    unfold onlineMixtureError clip
    fun_prop
  have hexpmeas : Measurable (fun u => Real.exp (-onlineMixtureError E η Y b x u)) := hnegmeas.exp
  have hqg : Integrable (fun z => physicalMixtureDensity E c a centers q z * g z)
      (euclideanGaussianLaw E) :=
    (integrable_physicalGaussianMixtureLaw_iff E c a centers hq hnegmeas).mp
      (onlineMixtureError_integrable E c a η centers hq Y b x).neg
  have hvg : Integrable (fun z => physicalMixtureDensity E c a centers p z * Real.exp (g z))
      (euclideanGaussianLaw E) :=
    (integrable_physicalGaussianMixtureLaw_iff E c a centers hp hexpmeas).mp
      (onlineMixtureError_exp_integrable E c a η centers hp Y b x)
  have h := density_pair_entropy_variational
    (q := physicalMixtureDensity E c a centers q) (v := physicalMixtureDensity E c a centers p) (g := g)
    (fun z => mixtureDensity_pos (fun _i _z => Real.exp_pos _) hq z)
    (fun z => mixtureDensity_pos (fun _i _z => Real.exp_pos _) hp z)
    (mixtureDensity_integrable (fun i => gaussianExponentialDensity_integrable E (a⁻¹ • (centers i - c))) q)
    (mixtureDensity_normalized
      (fun i => gaussianExponentialDensity_integrable E (a⁻¹ • (centers i - c)))
      (fun i => gaussianExponentialDensity_normalized E (a⁻¹ • (centers i - c))) hq)
    hqg (gaussian_mixture_relative_entropy_integrable E _ hq hp) hvg
  have hleft := integral_physicalGaussianMixtureLaw E c a centers hq hnegmeas
  rw [integral_neg] at hleft
  have hright := integral_physicalGaussianMixtureLaw E c a centers hp hexpmeas
  change onlineMixtureW E c a η centers p Y b x = _ at hright
  change -(∫ u, onlineMixtureError E η Y b x u ∂physicalGaussianMixtureLaw E c a centers q) =
    (∫ z, physicalMixtureDensity E c a centers q z * g z ∂euclideanGaussianLaw E) at hleft
  rw [← hleft, ← hright] at h
  exact h

/-- Holds for every candidate mixture, and therefore for the actual approximate update. -/
theorem gaussian_online_stability_bound (c : E) {a η β M : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) (hβ : 0 < β) (hM : 0 ≤ M)
    (centers : ι → E) {q p : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (Y b : E) (hb : ‖b‖ ≤ M) :
    mirrorStability
      (gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
      (gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
      (observedClippedLoss E c a η centers (Y, p)) p q ≤
      η ^ 2 * M ^ 2 / (2 * β) +
        Real.log (onlineMixtureW E c a η centers p Y b (finiteMixtureMean centers p)) := by
  have hvar := gaussian_online_error_variational E c a η centers hq hp Y b (finiteMixtureMean centers p)
  rw [onlineMixtureError_integral E c ha η centers hq p Y b] at hvar
  have hquad := quadratic_mean_penalty_bound hβ hη hM hb
    (finiteMixtureMean centers q - finiteMixtureMean centers p)
  unfold mirrorStability
  rw [gaussian_mixture_generator_bregman E _ β (finiteMixtureMean centers) hq hp]
  change _ ≤ _ at hvar
  linarith

end HeavyTail.GaussianEntropy
