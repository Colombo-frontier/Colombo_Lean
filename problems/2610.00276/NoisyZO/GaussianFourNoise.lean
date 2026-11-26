import NoisyZO.SphericalEstimator
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Four fresh Gaussian noises

The explicit `β = 4` estimator uses four independent standard Gaussian
values.  This file constructs their product law and discharges the scalar
mean/variance calculation used by the estimator moment theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace Gradient

namespace NoisyZO

noncomputable section

def standardGaussian : Measure ℝ := gaussianReal 0 1

def independentGaussianPair : Measure (ℝ × ℝ) :=
  standardGaussian.prod standardGaussian

/-- Outer and inner query pairs, mutually independent. -/
def fourNoiseMeasure : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  independentGaussianPair.prod independentGaussianPair

instance standardGaussian_isProbability : IsProbabilityMeasure standardGaussian := by
  dsimp [standardGaussian]
  infer_instance

instance independentGaussianPair_isProbability :
    IsProbabilityMeasure independentGaussianPair := by
  dsimp [independentGaussianPair]
  infer_instance

instance fourNoiseMeasure_isProbability : IsProbabilityMeasure fourNoiseMeasure := by
  dsimp [fourNoiseMeasure]
  infer_instance

instance fourNoiseMeasure_isFinite : IsFiniteMeasure fourNoiseMeasure := by
  dsimp [fourNoiseMeasure, independentGaussianPair, standardGaussian]
  infer_instance

theorem standardGaussian_mean :
    (∫ x, x ∂standardGaussian) = 0 := by
  simp [standardGaussian]

theorem standardGaussian_secondMoment :
    (∫ x, x ^ 2 ∂standardGaussian) = 1 := by
  have hvar := ProbabilityTheory.variance_fun_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simpa [standardGaussian] using hvar

theorem standardGaussian_integrable_id :
    Integrable (fun x : ℝ ↦ x) standardGaussian := by
  exact (ProbabilityTheory.memLp_id_gaussianReal'
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0∞)
    (by norm_num)).integrable (by norm_num)

theorem standardGaussian_integrable_sq :
    Integrable (fun x : ℝ ↦ x ^ 2) standardGaussian := by
  exact (ProbabilityTheory.memLp_id_gaussianReal'
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0∞)
    (by norm_num)).integrable_sq

def gaussianPairDifference (z : ℝ × ℝ) : ℝ := z.1 - z.2

theorem gaussianPairDifference_integrable :
    Integrable gaussianPairDifference independentGaussianPair := by
  exact (standardGaussian_integrable_id.comp_fst standardGaussian).sub
    (standardGaussian_integrable_id.comp_snd standardGaussian)

theorem gaussianPairDifference_sq_integrable :
    Integrable (fun z ↦ gaussianPairDifference z ^ 2)
      independentGaussianPair := by
  have hfstSq := standardGaussian_integrable_sq.comp_fst standardGaussian
  have hsndSq := standardGaussian_integrable_sq.comp_snd standardGaussian
  have hcross := standardGaussian_integrable_id.mul_prod
    standardGaussian_integrable_id
  apply Integrable.congr
    ((hfstSq.add (hcross.const_mul (-2))).add hsndSq)
  filter_upwards with z
  dsimp [gaussianPairDifference]
  ring

theorem integral_gaussianPairDifference :
    (∫ z, gaussianPairDifference z ∂independentGaussianPair) = 0 := by
  change (∫ z : ℝ × ℝ, z.1 - z.2
    ∂standardGaussian.prod standardGaussian) = 0
  rw [integral_sub
      (standardGaussian_integrable_id.comp_fst standardGaussian)
      (standardGaussian_integrable_id.comp_snd standardGaussian),
    integral_fun_fst (μ := standardGaussian) (ν := standardGaussian) (fun x : ℝ ↦ x),
    integral_fun_snd (μ := standardGaussian) (ν := standardGaussian) (fun x : ℝ ↦ x)]
  simp [standardGaussian_mean]

theorem integral_gaussianPairDifference_sq :
    (∫ z, gaussianPairDifference z ^ 2 ∂independentGaussianPair) = 2 := by
  have hfstSq := standardGaussian_integrable_sq.comp_fst standardGaussian
  have hsndSq := standardGaussian_integrable_sq.comp_snd standardGaussian
  have hcross := standardGaussian_integrable_id.mul_prod
    standardGaussian_integrable_id
  change (∫ z, gaussianPairDifference z ^ 2
    ∂standardGaussian.prod standardGaussian) = 2
  calc
    (∫ z, gaussianPairDifference z ^ 2
      ∂standardGaussian.prod standardGaussian) =
        ∫ z, (z.1 ^ 2 - 2 * (z.1 * z.2)) + z.2 ^ 2
          ∂standardGaussian.prod standardGaussian := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [gaussianPairDifference]
      ring
    _ = (∫ z, z.1 ^ 2 - 2 * (z.1 * z.2)
          ∂standardGaussian.prod standardGaussian) +
        ∫ z, z.2 ^ 2 ∂standardGaussian.prod standardGaussian := by
      exact integral_add (hfstSq.sub (hcross.const_mul 2)) hsndSq
    _ = ((∫ z, z.1 ^ 2 ∂standardGaussian.prod standardGaussian) -
        ∫ z, 2 * (z.1 * z.2) ∂standardGaussian.prod standardGaussian) +
        ∫ z, z.2 ^ 2 ∂standardGaussian.prod standardGaussian := by
      congr 2
      exact integral_sub hfstSq (hcross.const_mul 2)
    _ = 2 := by
      rw [integral_fun_fst (μ := standardGaussian) (ν := standardGaussian)
          (fun x : ℝ ↦ x ^ 2),
        integral_fun_snd (μ := standardGaussian) (ν := standardGaussian)
          (fun x : ℝ ↦ x ^ 2),
        integral_const_mul,
        integral_prod_mul (μ := standardGaussian) (ν := standardGaussian)
          (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)]
      simp [standardGaussian_mean, standardGaussian_secondMoment]
      norm_num

/-- The four independent standard Gaussian noises have exactly the scalar
second moment required by the explicit estimator. -/
theorem fourNoise_scalar_secondMoment :
    (∫ z, (betaFourNoiseScalar z.1.1 z.1.2 z.2.1 z.2.2) ^ 2
      ∂fourNoiseMeasure) = 130 := by
  apply integral_betaFourNoiseScalar_sq_eq fourNoiseMeasure
    (fun z ↦ z.1.1) (fun z ↦ z.1.2) (fun z ↦ z.2.1) (fun z ↦ z.2.2)
  · simpa only [gaussianPairDifference, fourNoiseMeasure] using
      gaussianPairDifference_sq_integrable.comp_snd independentGaussianPair
  · simpa only [gaussianPairDifference, fourNoiseMeasure] using
      gaussianPairDifference_sq_integrable.comp_fst independentGaussianPair
  · apply Integrable.congr
      (gaussianPairDifference_integrable.mul_prod gaussianPairDifference_integrable)
    filter_upwards with z
    dsimp [gaussianPairDifference]
    ring
  · simpa only [gaussianPairDifference, fourNoiseMeasure] using
      (show (∫ z, gaussianPairDifference z.2 ^ 2
        ∂independentGaussianPair.prod independentGaussianPair) = 2 by
          rw [integral_fun_snd (μ := independentGaussianPair)
            (ν := independentGaussianPair) (fun z ↦ gaussianPairDifference z ^ 2),
            integral_gaussianPairDifference_sq]
          simp)
  · simpa only [gaussianPairDifference, fourNoiseMeasure] using
      (show (∫ z, gaussianPairDifference z.1 ^ 2
        ∂independentGaussianPair.prod independentGaussianPair) = 2 by
          rw [integral_fun_fst (μ := independentGaussianPair)
            (ν := independentGaussianPair) (fun z ↦ gaussianPairDifference z ^ 2),
            integral_gaussianPairDifference_sq]
          simp)
  · simpa only [gaussianPairDifference, fourNoiseMeasure] using
      (show (∫ z, gaussianPairDifference z.2 * gaussianPairDifference z.1
        ∂independentGaussianPair.prod independentGaussianPair) = 0 by
          calc
            (∫ z, gaussianPairDifference z.2 * gaussianPairDifference z.1
              ∂independentGaussianPair.prod independentGaussianPair) =
                ∫ z, gaussianPairDifference z.1 * gaussianPairDifference z.2
                  ∂independentGaussianPair.prod independentGaussianPair := by
              apply integral_congr_ae
              filter_upwards with z
              ring
            _ = (∫ z, gaussianPairDifference z ∂independentGaussianPair) *
                ∫ z, gaussianPairDifference z ∂independentGaussianPair :=
              integral_prod_mul gaussianPairDifference gaussianPairDifference
            _ = 0 := by rw [integral_gaussianPairDifference]; simp)

theorem fourNoise_scalar_mean :
    (∫ z, betaFourNoiseScalar z.1.1 z.1.2 z.2.1 z.2.2
      ∂fourNoiseMeasure) = 0 := by
  change (∫ z, 8 * gaussianPairDifference z.2 - gaussianPairDifference z.1
    ∂independentGaussianPair.prod independentGaussianPair) = 0
  rw [integral_sub
      (gaussianPairDifference_integrable.comp_snd independentGaussianPair |>.const_mul 8)
      (gaussianPairDifference_integrable.comp_fst independentGaussianPair),
    integral_const_mul,
    integral_fun_snd (μ := independentGaussianPair) (ν := independentGaussianPair)
      gaussianPairDifference,
    integral_fun_fst (μ := independentGaussianPair) (ν := independentGaussianPair)
      gaussianPairDifference,
    integral_gaussianPairDifference]
  simp

/-- Combining an independent uniform direction with the four-Gaussian law
gives the exact vector-noise second moment `65 d²/(18h²)`. -/
theorem integral_norm_betaFourGaussianNoise_sq_eq
    {d : ℕ} (hd : 0 < d) {h : ℝ} (hh : h ≠ 0) :
    (∫ z, ‖betaFourSphericalNoise d h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2‖ ^ 2
      ∂(uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) =
      65 * d ^ 2 / (18 * h ^ 2) := by
  apply integral_norm_betaFourSphericalNoise_sq_eq
    ((uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure)
    d hh (fun z ↦ z.1)
    (fun z ↦ z.2.1.1) (fun z ↦ z.2.1.2)
    (fun z ↦ z.2.2.1) (fun z ↦ z.2.2.2)
  · have hp : MeasurableSet
        {z : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) | ‖z.1‖ = 1} := by
      exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards [uniformUnitSphere_norm_eq_one hd] with u hu
    exact Filter.Eventually.of_forall fun _noise ↦ hu
  · calc
      (∫ z, (betaFourNoiseScalar
          z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) ^ 2
        ∂(uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) =
          (uniformUnitSphere d hd : Measure (Point d)).real Set.univ •
            ∫ noise, (betaFourNoiseScalar
              noise.1.1 noise.1.2 noise.2.1 noise.2.2) ^ 2
              ∂fourNoiseMeasure := by
        exact integral_fun_snd
          (fun noise : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ (betaFourNoiseScalar
            noise.1.1 noise.1.2 noise.2.1 noise.2.2) ^ 2)
      _ = 130 := by rw [fourNoise_scalar_secondMoment]; simp

/-- Under the concrete product of a uniform direction and four fresh Gaussian
noises, the explicit estimator has the full `229 d²/h²` second-moment bound. -/
theorem NormalizedObjective.integral_norm_betaFourGaussianEstimator_sq_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    (∫ z, ‖betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2‖ ^ 2
      ∂(uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) ≤
      229 * d ^ 2 / h ^ 2 := by
  let μ : Measure (Point d × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let signal : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalSignal d F.f x h z.1
  let noise : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalNoise d h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  have hu : ∀ᵐ z ∂μ, ‖z.1‖ = 1 := by
    have hp : MeasurableSet
        {z : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) | ‖z.1‖ = 1} := by
      exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
    dsimp only [μ]
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards [uniformUnitSphere_norm_eq_one hd] with u hu
    exact Filter.Eventually.of_forall fun _noise ↦ hu
  have hsignalMeas : AEStronglyMeasurable (fun z ↦ ‖signal z‖ ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [signal, μ]
    unfold betaFourSphericalSignal centralDifferenceSignal
    have hf : Continuous F.f := F.smooth.continuous
    fun_prop
  have hsignalBound : ∀ᵐ z ∂μ, ‖signal z‖ ^ 2 ≤ 225 * d ^ 2 := by
    filter_upwards [hu] with z hunit
    have hnorm := F.norm_betaFourSphericalSignal_le x hh hh1 z.1 hunit hx
    calc
      ‖signal z‖ ^ 2 ≤ (15 * (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
      _ = 225 * d ^ 2 := by ring
  have hsignalSq : Integrable (fun z ↦ ‖signal z‖ ^ 2) μ :=
    (integrable_const (225 * (d : ℝ) ^ 2)).mono' hsignalMeas (by
      filter_upwards [hsignalBound] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz)
  have hnoiseMoment : (∫ z, ‖noise z‖ ^ 2 ∂μ) =
      65 * d ^ 2 / (18 * h ^ 2) := by
    dsimp only [noise, μ]
    exact integral_norm_betaFourGaussianNoise_sq_eq hd hh.ne'
  have hnoiseSq : Integrable (fun z ↦ ‖noise z‖ ^ 2) μ := by
    apply Integrable.of_integral_ne_zero
    rw [hnoiseMoment]
    positivity
  have hnoiseMeas : AEStronglyMeasurable noise μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [noise, μ]
    unfold betaFourSphericalNoise centralDifferenceNoise
    fun_prop
  have hnoiseInt : Integrable noise μ := by
    have hmem : MemLp noise 2 μ :=
      (memLp_two_iff_integrable_sq_norm hnoiseMeas).2 hnoiseSq
    exact hmem.integrable (by norm_num)
  have hcrossInt : Integrable (fun z ↦ ⟪signal z, noise z⟫_ℝ) μ := by
    have hmeas : AEStronglyMeasurable (fun z ↦ ⟪signal z, noise z⟫_ℝ) μ := by
      apply Continuous.aestronglyMeasurable
      dsimp only [signal, noise, μ]
      unfold betaFourSphericalSignal centralDifferenceSignal
      unfold betaFourSphericalNoise centralDifferenceNoise
      have hf : Continuous F.f := F.smooth.continuous
      fun_prop
    apply (hnoiseInt.norm.const_mul (15 * (d : ℝ))).mono' hmeas
    filter_upwards [hu] with z hunit
    rw [Real.norm_eq_abs]
    calc
      |⟪signal z, noise z⟫_ℝ| ≤ ‖signal z‖ * ‖noise z‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (15 * d) * ‖noise z‖ := by
        gcongr
        exact F.norm_betaFourSphericalSignal_le x hh hh1 z.1 hunit hx
  have hcross : (∫ z, ⟪signal z, noise z⟫_ℝ ∂μ) = 0 := by
    let A : Point d → ℝ := fun u ↦
      ((d : ℝ) / (6 * h)) *
        ⟪betaFourSphericalSignal d F.f x h u, u⟫_ℝ
    have hpoint : ∀ z : Point d × ((ℝ × ℝ) × (ℝ × ℝ)),
        ⟪signal z, noise z⟫_ℝ = A z.1 *
          betaFourNoiseScalar z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2 := by
      intro z
      dsimp only [signal, noise, A]
      rw [betaFourSphericalNoise_eq d hh.ne' z.1,
        real_inner_smul_right]
      ring
    calc
      (∫ z, ⟪signal z, noise z⟫_ℝ ∂μ) =
          ∫ z, A z.1 * betaFourNoiseScalar
            z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (∫ u, A u ∂(uniformUnitSphere d hd : Measure (Point d))) *
          ∫ ξ, betaFourNoiseScalar ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2
            ∂fourNoiseMeasure := by
        dsimp only [μ]
        exact integral_prod_mul A
          (fun ξ : ((ℝ × ℝ) × (ℝ × ℝ)) ↦
            betaFourNoiseScalar ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2)
      _ = 0 := by rw [fourNoise_scalar_mean, mul_zero]
  change (∫ z, ‖betaFourSphericalEstimator d F.f x h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2‖ ^ 2 ∂μ) ≤ _
  apply F.integral_norm_betaFourSphericalEstimator_sq_le μ x hh hh1
    (fun z ↦ z.1)
    (fun z ↦ z.2.1.1) (fun z ↦ z.2.1.2)
    (fun z ↦ z.2.2.1) (fun z ↦ z.2.2.2)
    hu
  · simpa only [signal] using hsignalSq
  · simpa only [signal, noise] using hcrossInt
  · simpa only [noise] using hnoiseSq
  · simpa only [signal, noise] using hcross
  · simpa only [noise] using hnoiseMoment
  · exact hx

/-- The concrete four-query estimator is square-integrable under the product
of the uniform direction and four fresh Gaussian noises. -/
theorem NormalizedObjective.betaFourGaussianEstimator_sq_integrable
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    Integrable (fun z ↦ ‖betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2‖ ^ 2)
      ((uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) := by
  let μ : Measure (Point d × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let signal : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalSignal d F.f x h z.1
  let noise : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalNoise d h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  have hu : ∀ᵐ z ∂μ, ‖z.1‖ = 1 := by
    have hp : MeasurableSet
        {z : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) | ‖z.1‖ = 1} := by
      exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
    dsimp only [μ]
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards [uniformUnitSphere_norm_eq_one hd] with u hu
    exact Filter.Eventually.of_forall fun _noise ↦ hu
  have hsignalSqMeas : AEStronglyMeasurable (fun z ↦ ‖signal z‖ ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [signal, μ]
    unfold betaFourSphericalSignal centralDifferenceSignal
    have hf : Continuous F.f := F.smooth.continuous
    fun_prop
  have hsignalSq : Integrable (fun z ↦ ‖signal z‖ ^ 2) μ := by
    apply (integrable_const (225 * (d : ℝ) ^ 2)).mono' hsignalSqMeas
    filter_upwards [hu] with z hunit
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hs : ‖signal z‖ ≤ 15 * (d : ℝ) := by
      simpa only [signal] using
        F.norm_betaFourSphericalSignal_le x hh hh1 z.1 hunit hx
    calc
      ‖signal z‖ ^ 2 ≤ (15 * (d : ℝ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hs
      _ = 225 * (d : ℝ) ^ 2 := by ring
  have hnoiseMoment : (∫ z, ‖noise z‖ ^ 2 ∂μ) =
      65 * d ^ 2 / (18 * h ^ 2) := by
    dsimp only [noise, μ]
    exact integral_norm_betaFourGaussianNoise_sq_eq hd hh.ne'
  have hnoiseSq : Integrable (fun z ↦ ‖noise z‖ ^ 2) μ := by
    apply Integrable.of_integral_ne_zero
    rw [hnoiseMoment]
    positivity
  have hestMeas : AEStronglyMeasurable
      (fun z ↦ ‖betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2‖ ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    unfold betaFourSphericalEstimator betaFourSphericalSignal
      centralDifferenceSignal betaFourSphericalNoise centralDifferenceNoise
    have hf : Continuous F.f := F.smooth.continuous
    fun_prop
  apply ((hsignalSq.const_mul 2).add (hnoiseSq.const_mul 2)).mono' hestMeas
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖signal z + noise z‖ ^ 2 ≤
    2 * ‖signal z‖ ^ 2 + 2 * ‖noise z‖ ^ 2
  have hadd := norm_add_le (signal z) (noise z)
  nlinarith [sq_nonneg (‖signal z‖ - ‖noise z‖),
    norm_nonneg (signal z + noise z)]

/-- In particular, the concrete four-query estimator is Bochner integrable. -/
theorem NormalizedObjective.betaFourGaussianEstimator_integrable
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (x : Point d) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : ‖x‖ ≤ 1) :
    Integrable (fun z ↦ betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)
      ((uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) := by
  let μ : Measure (Point d × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let estimator : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalEstimator d F.f x h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  have hmeas : AEStronglyMeasurable estimator μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [estimator, μ]
    unfold betaFourSphericalEstimator betaFourSphericalSignal
      centralDifferenceSignal betaFourSphericalNoise centralDifferenceNoise
    have hf : Continuous F.f := F.smooth.continuous
    fun_prop
  have hsq : Integrable (fun z ↦ ‖estimator z‖ ^ 2) μ := by
    simpa only [estimator, μ] using
      F.betaFourGaussianEstimator_sq_integrable hd x hh hh1 hx
  exact ((memLp_two_iff_integrable_sq_norm hmeas).2 hsq).integrable (by norm_num)

/-- All probabilistic and geometric premises for the explicit estimator mean
are discharged by the concrete uniform-direction/four-Gaussian product law. -/
theorem NormalizedObjective.norm_integral_betaFourGaussianEstimator_sub_gradient_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d) (x : Point d)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hx : ‖x‖ ≤ 1) :
    ‖(∫ z, betaFourSphericalEstimator d F.f x h z.1
        z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
      ∂(uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure) -
        ∇ F.f x‖ ≤ h ^ 3 / 12 := by
  let μ : Measure (Point d × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (uniformUnitSphere d hd : Measure (Point d)).prod fourNoiseMeasure
  let signal : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalSignal d F.f x h z.1
  let noise : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) → Point d :=
    fun z ↦ betaFourSphericalNoise d h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2
  have hu : ∀ᵐ z ∂μ, ‖z.1‖ = 1 := by
    have hp : MeasurableSet
        {z : Point d × ((ℝ × ℝ) × (ℝ × ℝ)) | ‖z.1‖ = 1} := by
      exact (measurableSet_singleton (1 : ℝ)).preimage (by fun_prop)
    dsimp only [μ]
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards [uniformUnitSphere_norm_eq_one hd] with u hu
    exact Filter.Eventually.of_forall fun _noise ↦ hu
  have hsignalMeas : AEStronglyMeasurable signal μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [signal, μ]
    unfold betaFourSphericalSignal centralDifferenceSignal
    have hf : Continuous F.f := F.smooth.continuous
    fun_prop
  have hsignal : Integrable signal μ := by
    apply (integrable_const (15 * (d : ℝ))).mono' hsignalMeas
    filter_upwards [hu] with z hunit
    exact F.norm_betaFourSphericalSignal_le x hh hh1 z.1 hunit hx
  have hnoiseMoment : (∫ z, ‖noise z‖ ^ 2 ∂μ) =
      65 * d ^ 2 / (18 * h ^ 2) := by
    dsimp only [noise, μ]
    exact integral_norm_betaFourGaussianNoise_sq_eq hd hh.ne'
  have hnoiseSq : Integrable (fun z ↦ ‖noise z‖ ^ 2) μ := by
    apply Integrable.of_integral_ne_zero
    rw [hnoiseMoment]
    positivity
  have hnoiseMeas : AEStronglyMeasurable noise μ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [noise, μ]
    unfold betaFourSphericalNoise centralDifferenceNoise
    fun_prop
  have hnoise : Integrable noise μ := by
    have hmem : MemLp noise 2 μ :=
      (memLp_two_iff_integrable_sq_norm hnoiseMeas).2 hnoiseSq
    exact hmem.integrable (by norm_num)
  have hnoiseMean : (∫ z, noise z ∂μ) = 0 := by
    have hinner : ∀ u : Point d,
        (∫ ξ, betaFourSphericalNoise d h u
          ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2 ∂fourNoiseMeasure) = 0 := by
      intro u
      rw [show (fun ξ : ((ℝ × ℝ) × (ℝ × ℝ)) ↦
          betaFourSphericalNoise d h u
            ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2) =
          (fun ξ ↦ (((d : ℝ) / (6 * h)) *
            betaFourNoiseScalar ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2) • u) by
        funext ξ
        exact betaFourSphericalNoise_eq d hh.ne' u _ _ _ _]
      rw [integral_smul_const, integral_const_mul, fourNoise_scalar_mean,
        mul_zero, zero_smul]
    calc
      (∫ z, noise z ∂μ) =
          ∫ u, ∫ ξ, betaFourSphericalNoise d h u
            ξ.1.1 ξ.1.2 ξ.2.1 ξ.2.2 ∂fourNoiseMeasure
            ∂(uniformUnitSphere d hd : Measure (Point d)) := by
        dsimp only [noise, μ]
        exact integral_prod _ hnoise
      _ = ∫ _u : Point d, (0 : Point d)
          ∂(uniformUnitSphere d hd : Measure (Point d)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = 0 := by simp
  have hsignalMean : (∫ z, signal z ∂μ) =
      betaFourBallField d (∇ F.f) x h := by
    calc
      (∫ z, signal z ∂μ) = fourNoiseMeasure.real Set.univ •
          ∫ u, betaFourSphericalSignal d F.f x h u
            ∂(uniformUnitSphere d hd : Measure (Point d)) := by
        dsimp only [signal, μ]
        exact integral_fun_fst _
      _ = betaFourBallField d (∇ F.f) x h := by
        rw [integral_betaFourSphericalSignal_eq_betaFourBallField
          hd F.f (F.smooth.of_le (by
            norm_cast
            exact le_trans (by omega : 1 ≤ 2) o.two_le_k)) x hh]
        simp
  change ‖(∫ z, betaFourSphericalEstimator d F.f x h z.1
      z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2 ∂μ) - ∇ F.f x‖ ≤ _
  apply F.norm_integral_betaFourSphericalEstimator_sub_gradient_le
    μ hbeta x hh hh1
    (fun z ↦ z.1)
    (fun z ↦ z.2.1.1) (fun z ↦ z.2.1.2)
    (fun z ↦ z.2.2.1) (fun z ↦ z.2.2.2)
  · simpa only [signal] using hsignal
  · simpa only [noise] using hnoise
  · simpa only [signal] using hsignalMean
  · simpa only [noise] using hnoiseMean
  · exact hx

end

end NoisyZO
