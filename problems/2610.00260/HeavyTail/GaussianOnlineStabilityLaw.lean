import HeavyTail.GaussianOnlineStabilityPullback

/-! The exponential-density definition of the learner is exactly a finite
mixture of translated, scaled standard Gaussian laws. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem densityMeasure_mixture_eq_sum (μ : Measure Ω) (φ : ι → Ω → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (hφpos : ∀ i z, 0 ≤ φ i z)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    densityMeasure μ (mixtureDensity φ w) =
      Measure.sum (fun i => ENNReal.ofReal (w i) • densityMeasure μ (φ i)) := by
  have he : (fun z => ENNReal.ofReal (mixtureDensity φ w z)) =
      ∑' i, ENNReal.ofReal (w i) • (fun z => ENNReal.ofReal (φ i z)) := by
    funext z
    simp only [tsum_fintype, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mixtureDensity_eq_sum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hφpos i z))]
    exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hw i))
  unfold densityMeasure
  have hm (i : ι) : Measurable (ENNReal.ofReal (w i) • (fun z => ENNReal.ofReal (φ i z))) :=
    measurable_const.mul (hφ i).ennreal_ofReal
  rw [he, withDensity_tsum hm]
  congr 1
  funext i
  exact withDensity_smul _ (hφ i).ennreal_ofReal

namespace GaussianEntropy
open GaussianEstimates

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_component_physical_law (c center : E) {a : ℝ} (ha : a ≠ 0) :
    (densityMeasure (euclideanGaussianLaw E)
      (gaussianExponentialDensity E (a⁻¹ • (center - c)))).map (fun z => c + a • z) =
        (euclideanGaussianLaw E).map (fun z => center + a • z) := by
  rw [gaussianExponentialDensity_measure,
    Measure.map_map (show Measurable (fun z : E => c + a • z) by fun_prop)
      (show Measurable (fun z : E => a⁻¹ • (center - c) + z) by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_def, smul_add, smul_smul a a⁻¹, mul_inv_cancel₀ ha, one_smul]
  abel

theorem physicalGaussianMixtureLaw_eq_sum (c : E) {a : ℝ} (ha : a ≠ 0)
    (centers : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    physicalGaussianMixtureLaw E c a centers w =
      Measure.sum (fun i => ENNReal.ofReal (w i) •
        (euclideanGaussianLaw E).map (fun z => centers i + a • z)) := by
  unfold physicalGaussianMixtureLaw
  rw [densityMeasure_mixture_eq_sum _ (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c)))
    (fun i => (gaussianLogDensity_measurable E (a⁻¹ • (centers i - c))).exp)
    (fun _ _ => (Real.exp_pos _).le) w hw.1,
    Measure.map_sum (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul, gaussian_component_physical_law E c (centers i) ha]

theorem integral_physicalGaussianMixtureLaw_sum (c : E) {a : ℝ} (ha : a ≠ 0)
    (centers : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    {f : E → ℝ} (hf : Measurable f)
    (hi : ∀ i, Integrable (fun z => f (centers i + a • z)) (euclideanGaussianLaw E)) :
    (∫ u, f u ∂physicalGaussianMixtureLaw E c a centers w) =
      ∑ i, w i * ∫ z, f (centers i + a • z) ∂euclideanGaussianLaw E := by
  have him (i : ι) : Integrable f ((euclideanGaussianLaw E).map (fun z => centers i + a • z)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (show Measurable (fun z : E => centers i + a • z) by fun_prop).aemeasurable).mpr (hi i)
  rw [physicalGaussianMixtureLaw_eq_sum E c ha centers hw, Measure.sum_fintype]
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hw.1 i), smul_eq_mul,
      integral_map (show Measurable (fun z : E => centers i + a • z) by fun_prop).aemeasurable
        hf.aestronglyMeasurable]
  · intro i _
    exact (him i).smul_measure ENNReal.ofReal_ne_top

end GaussianEntropy
end HeavyTail
