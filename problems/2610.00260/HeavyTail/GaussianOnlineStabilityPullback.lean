import HeavyTail.GaussianOnlineStabilityIntegrals

/-! Change of variables, integrability and first moments of the actual online
error under the physical finite Gaussian-mixture probability laws. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

abbrev physicalMixtureDensity (c : E) (a : ℝ) (centers : ι → E) (w : ι → ℝ) : E → ℝ :=
  mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) w

theorem integral_physicalGaussianMixtureLaw (c : E) (a : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) {f : E → ℝ} (hf : Measurable f) :
    (∫ u, f u ∂physicalGaussianMixtureLaw E c a centers w) =
      ∫ z, physicalMixtureDensity E c a centers w z * f (c + a • z) ∂euclideanGaussianLaw E := by
  rw [physicalGaussianMixtureLaw,
    integral_map (f := f) (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable
      hf.aestronglyMeasurable,
    integral_densityMeasure (w := physicalMixtureDensity E c a centers w)
      (mixtureDensity_measurable (fun i => (gaussianLogDensity_measurable E (a⁻¹ • (centers i - c))).exp) w)
      (fun z => (mixtureDensity_pos (fun _i _z => Real.exp_pos _) hw z).le)]

theorem integrable_physicalGaussianMixtureLaw_iff (c : E) (a : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) {f : E → ℝ} (hf : Measurable f) :
    Integrable f (physicalGaussianMixtureLaw E c a centers w) ↔
      Integrable (fun z => physicalMixtureDensity E c a centers w z * f (c + a • z))
        (euclideanGaussianLaw E) := by
  rw [physicalGaussianMixtureLaw,
    integrable_map_measure (g := f) hf.aestronglyMeasurable
      (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable]
  simpa only [Function.comp_def, smul_eq_mul] using
    integrable_densityMeasure_iff_vector (w := physicalMixtureDensity E c a centers w)
      (mixtureDensity_measurable (fun i => (gaussianLogDensity_measurable E (a⁻¹ • (centers i - c))).exp) w)
      (fun z => (mixtureDensity_pos (fun _i _z => Real.exp_pos _) hw z).le)
      (fun z => f (c + a • z))

theorem physical_mixture_inner_integrable (c : E) (a : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (b x : E) :
    Integrable (fun u => ⟪b, u - x⟫_ℝ) (physicalGaussianMixtureLaw E c a centers w) := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hw
  exact (innerSL ℝ b).integrable_comp
    ((physicalGaussianMixtureLaw_id_integrable E c a centers hw).sub (integrable_const x))

theorem physical_mixture_inner_integral (c : E) {a : ℝ} (ha : a ≠ 0) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (b x : E) :
    (∫ u, ⟪b, u - x⟫_ℝ ∂physicalGaussianMixtureLaw E c a centers w) =
      ⟪b, finiteMixtureMean centers w - x⟫_ℝ := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hw
  have hi : Integrable (fun u : E => u - x) (physicalGaussianMixtureLaw E c a centers w) :=
    (physicalGaussianMixtureLaw_id_integrable E c a centers hw).sub (integrable_const x)
  change (∫ u, (innerSL ℝ b) (u - x) ∂physicalGaussianMixtureLaw E c a centers w) = _
  rw [(innerSL ℝ b).integral_comp_comm hi,
    integral_sub (physicalGaussianMixtureLaw_id_integrable E c a centers hw) (integrable_const x),
    physicalGaussianMixtureLaw_mean E c ha centers hw]
  simp

theorem physical_mixture_clip_integrable (c : E) (a η : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y x : E) :
    Integrable (fun u => clip (η * ⟪Y, u - x⟫_ℝ)) (physicalGaussianMixtureLaw E c a centers w) := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hw
  apply (integrable_const (1 : ℝ)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold clip
    fun_prop
  · exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using abs_le.mpr (clip_mem _))

theorem physical_mixture_clip_integral_bound (c : E) (a η : ℝ) (centers : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (Y x : E) :
    |∫ u, clip (η * ⟪Y, u - x⟫_ℝ) ∂physicalGaussianMixtureLaw E c a centers w| ≤ 1 := by
  letI := physicalGaussianMixtureLaw_probability E c a centers hw
  have h := norm_integral_le_of_norm_le_const (μ := physicalGaussianMixtureLaw E c a centers w)
    (f := fun u => clip (η * ⟪Y, u - x⟫_ℝ))
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using abs_le.mpr (clip_mem (η * ⟪Y, u - x⟫_ℝ))))
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using h

def onlineMixtureError (η : ℝ) (Y b x u : E) : ℝ :=
  clip (η * ⟪Y, u - x⟫_ℝ) - η * ⟪b, u - x⟫_ℝ

theorem onlineMixtureError_integrable (c : E) (a η : ℝ) (centers : ι → E)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (Y b x : E) :
    Integrable (onlineMixtureError E η Y b x) (physicalGaussianMixtureLaw E c a centers q) :=
  (physical_mixture_clip_integrable E c a η centers hq Y x).sub
    ((physical_mixture_inner_integrable E c a centers hq b x).const_mul η)

theorem onlineMixtureError_integral (c : E) {a : ℝ} (ha : a ≠ 0) (η : ℝ) (centers : ι → E)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (w : ι → ℝ) (Y b : E) :
    (∫ u, onlineMixtureError E η Y b (finiteMixtureMean centers w) u
      ∂physicalGaussianMixtureLaw E c a centers q) =
      observedClippedLoss E c a η centers (Y, w) q -
        η * ⟪b, finiteMixtureMean centers q - finiteMixtureMean centers w⟫_ℝ := by
  unfold onlineMixtureError
  rw [integral_sub (physical_mixture_clip_integrable E c a η centers hq Y _)
    ((physical_mixture_inner_integrable E c a centers hq b _).const_mul η),
    integral_const_mul, physical_mixture_inner_integral E c ha centers hq,
    ← observedClippedLoss_eq_expectation E c a η centers (Y, w) hq]

end HeavyTail.GaussianEntropy
