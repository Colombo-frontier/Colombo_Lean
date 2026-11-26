import HeavyTail.GaussianMeasurableUpdate
import HeavyTail.GaussianLowerMoments

/-! The quadratic mean map is the actual expectation of the Gaussian mixture.
Both tilted densities and their physical affine pushforwards are genuine
probability measures. All vector integrability is proved here. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι Ω V : Type*} [Fintype ι] [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def finiteMixtureMean (centers : ι → V) : (ι → ℝ) →L[ℝ] V :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (centers i)

theorem finiteMixtureMean_apply (centers : ι → V) (w : ι → ℝ) :
    finiteMixtureMean centers w = ∑ i, w i • centers i := by
  simp [finiteMixtureMean]

theorem finiteMixtureMean_mem_convex {S : Set V} (hS : Convex ℝ S)
    {centers : ι → V} (hc : ∀ i, centers i ∈ S) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) : finiteMixtureMean centers w ∈ S := by
  rw [finiteMixtureMean_apply]
  exact hS.sum_mem (fun i _ => hw.1 i) hw.2 (fun i _ => hc i)

theorem integral_densityMeasure_vector {μ : Measure Ω} {w : Ω → ℝ}
    (hwmeas : Measurable w) (hwnonneg : ∀ ω, 0 ≤ w ω) (g : Ω → V) :
    (∫ ω, g ω ∂densityMeasure μ w) = ∫ ω, w ω • g ω ∂μ := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul
    hwmeas.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hwnonneg _)]

theorem integrable_densityMeasure_iff_vector {μ : Measure Ω} {w : Ω → ℝ}
    (hwmeas : Measurable w) (hwnonneg : ∀ ω, 0 ≤ w ω) (g : Ω → V) :
    Integrable g (densityMeasure μ w) ↔ Integrable (fun ω => w ω • g ω) μ := by
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul'
    hwmeas.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hwnonneg _)]

namespace GaussianEntropy

open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_tilted_id_integrable (t : E) :
    Integrable (fun z : E => z)
      (densityMeasure (euclideanGaussianLaw E) (gaussianExponentialDensity E t)) := by
  rw [gaussianExponentialDensity_measure]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (show Measurable (fun z : E => t + z) by fun_prop).aemeasurable).mpr
  exact (integrable_const t).add (GaussianLower.gaussian_id_integrable E)

theorem gaussian_tilted_mean (t : E) :
    (∫ z : E, z ∂densityMeasure (euclideanGaussianLaw E) (gaussianExponentialDensity E t)) = t := by
  rw [gaussianExponentialDensity_measure,
    integral_map (f := fun z : E => z) (show Measurable (fun z : E => t + z) by fun_prop).aemeasurable
      measurable_id.aestronglyMeasurable,
    integral_add (integrable_const t) (GaussianLower.gaussian_id_integrable E),
    GaussianLower.gaussian_vector_mean_zero]
  simp

theorem gaussian_weighted_id_integrable (t : E) :
    Integrable (fun z => gaussianExponentialDensity E t z • z) (euclideanGaussianLaw E) :=
  (integrable_densityMeasure_iff_vector (gaussianLogDensity_measurable E t).exp
    (fun _ => (Real.exp_pos _).le) (fun z : E => z)).mp (gaussian_tilted_id_integrable E t)

theorem gaussian_weighted_mean (t : E) :
    (∫ z, gaussianExponentialDensity E t z • z ∂euclideanGaussianLaw E) = t := by
  rw [← integral_densityMeasure_vector (w := gaussianExponentialDensity E t)
    (gaussianLogDensity_measurable E t).exp
    (fun _ => (Real.exp_pos _).le) (fun z : E => z), gaussian_tilted_mean]

theorem gaussian_mixture_weighted_id_integrable (t : ι → E) (w : ι → ℝ) :
    Integrable (fun z => mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w z • z)
      (euclideanGaussianLaw E) := by
  have heq : (fun z => mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w z • z) =
      (fun z => ∑ i, w i • (gaussianExponentialDensity E (t i) z • z)) := by
    funext z
    rw [mixtureDensity_eq_sum, Finset.sum_smul]
    simp only [mul_smul]
  rw [heq]
  exact integrable_finset_sum _ (fun i _ => Integrable.smul (w i) (gaussian_weighted_id_integrable E (t i)))

theorem gaussian_mixture_id_integrable (t : ι → E) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (fun z : E => z)
      (densityMeasure (euclideanGaussianLaw E)
        (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w)) :=
  (integrable_densityMeasure_iff_vector
    (mixtureDensity_measurable (fun i => (gaussianLogDensity_measurable E (t i)).exp) w)
    (fun z => (mixtureDensity_pos (fun _i _z => Real.exp_pos _) hw z).le)
    (fun z : E => z)).mpr (gaussian_mixture_weighted_id_integrable E t w)

/-- Exact first moment of the actual density mixture, including zero weights. -/
theorem gaussian_mixture_mean (t : ι → E) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) :
    (∫ z : E, z ∂densityMeasure (euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w)) = finiteMixtureMean t w := by
  rw [integral_densityMeasure_vector
    (w := mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w)
    (mixtureDensity_measurable (fun i => (gaussianLogDensity_measurable E (t i)).exp) w)
    (fun z => (mixtureDensity_pos (fun _i _z => Real.exp_pos _) hw z).le) (fun z : E => z)]
  simp_rw [mixtureDensity_eq_sum, Finset.sum_smul, mul_smul]
  have hi (i : ι) : Integrable (fun z => w i • (gaussianExponentialDensity E (t i) z • z))
      (euclideanGaussianLaw E) := Integrable.smul (w i) (gaussian_weighted_id_integrable E (t i))
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  simp only [integral_smul, gaussian_weighted_mean, finiteMixtureMean_apply]

def physicalGaussianMixtureLaw (c : E) (a : ℝ) (centers : ι → E) (w : ι → ℝ) : Measure E :=
  (densityMeasure (euclideanGaussianLaw E)
    (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w)).map
      (fun z => c + a • z)

theorem gaussian_mixture_probability (t : ι → E) {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) :
    IsProbabilityMeasure (densityMeasure (euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (t i)) w)) :=
  mixtureDensity_probability (φ := fun i => gaussianExponentialDensity E (t i))
    (fun _i _z => Real.exp_pos _) (fun i => gaussianExponentialDensity_integrable E (t i))
    (fun i => gaussianExponentialDensity_normalized E (t i)) hw

theorem physicalGaussianMixtureLaw_probability (c : E) (a : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    IsProbabilityMeasure (physicalGaussianMixtureLaw E c a centers w) := by
  letI := gaussian_mixture_probability E (fun i => a⁻¹ • (centers i - c)) hw
  exact isProbabilityMeasure_map (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable

theorem physicalGaussianMixtureLaw_id_integrable (c : E) (a : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    Integrable (fun z : E => z) (physicalGaussianMixtureLaw E c a centers w) := by
  letI := gaussian_mixture_probability E (fun i => a⁻¹ • (centers i - c)) hw
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable).mpr
  exact (integrable_const c).add (Integrable.smul a (gaussian_mixture_id_integrable E _ hw))

/-- The physical Gaussian mixture mean is the weighted sum of its physical centers. -/
theorem physicalGaussianMixtureLaw_mean (c : E) {a : ℝ} (ha : a ≠ 0) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    (∫ z : E, z ∂physicalGaussianMixtureLaw E c a centers w) = finiteMixtureMean centers w := by
  letI := gaussian_mixture_probability E (fun i => a⁻¹ • (centers i - c)) hw
  have hi : Integrable (fun z : E => a • z) (densityMeasure (euclideanGaussianLaw E)
      (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w)) :=
    Integrable.smul a (gaussian_mixture_id_integrable E (fun i => a⁻¹ • (centers i - c)) hw)
  rw [physicalGaussianMixtureLaw,
    integral_map (f := fun z : E => z) (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable
      measurable_id.aestronglyMeasurable,
    integral_add (integrable_const c) hi,
    integral_smul, gaussian_mixture_mean E _ hw]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, finiteMixtureMean_apply]
  have hscale (i : ι) : a • (w i • (a⁻¹ • (centers i - c))) = w i • (centers i - c) := by
    rw [smul_comm a (w i), smul_smul a a⁻¹, mul_inv_cancel₀ ha, one_smul]
  have hsumScale : a • (∑ i, w i • (a⁻¹ • (centers i - c))) =
      ∑ i, w i • (centers i - c) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => hscale i)
  rw [hsumScale]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw.2, one_smul]
  abel

end GaussianEntropy
end HeavyTail
