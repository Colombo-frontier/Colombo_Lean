import HeavyTail.GaussianMeasurableUpdateMean
import HeavyTail.ScalarClipping

/-! The observed loss is an actual clipped Gaussian integral. Its bounded
integrand proves continuity and measurability in the observation and current
mixture. Composing it with the constructed selector gives the concrete
measurable online update, without an externally supplied loss operator. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates

variable {ι : Type*} [Fintype ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def observedComponentIntegrand (c : E) (a η : ℝ) (centers : ι → E)
    (i : ι) (p : E × (ι → ℝ)) (z : E) : ℝ :=
  gaussianExponentialDensity E (a⁻¹ • (centers i - c)) z *
    clip (η * ⟪p.1, c + a • z - finiteMixtureMean centers p.2⟫_ℝ)

def observedClippedLoss (c : E) (a η : ℝ) (centers : ι → E)
    (p : E × (ι → ℝ)) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (∫ z, observedComponentIntegrand E c a η centers i p z ∂euclideanGaussianLaw E) •
    ContinuousLinearMap.proj i

theorem observedComponentIntegrand_bound (c : E) (a η : ℝ) (centers : ι → E)
    (i : ι) (p : E × (ι → ℝ)) (z : E) :
    ‖observedComponentIntegrand E c a η centers i p z‖ ≤
      gaussianExponentialDensity E (a⁻¹ • (centers i - c)) z := by
  unfold observedComponentIntegrand
  have hpos : 0 < gaussianExponentialDensity E (a⁻¹ • (centers i - c)) z := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  exact (mul_le_mul_of_nonneg_left (abs_le.mpr (clip_mem _)) hpos.le).trans_eq (mul_one _)

theorem observedComponentIntegrand_integrable (c : E) (a η : ℝ) (centers : ι → E)
    (i : ι) (p : E × (ι → ℝ)) :
    Integrable (observedComponentIntegrand E c a η centers i p) (euclideanGaussianLaw E) := by
  apply (gaussianExponentialDensity_integrable E (a⁻¹ • (centers i - c))).mono'
  · apply Measurable.aestronglyMeasurable
    unfold observedComponentIntegrand gaussianExponentialDensity gaussianLogDensity clip
    fun_prop
  · exact ae_of_all _ (observedComponentIntegrand_bound E c a η centers i p)

theorem observedComponentIntegral_continuous (c : E) (a η : ℝ) (centers : ι → E) (i : ι) :
    Continuous (fun p => ∫ z, observedComponentIntegrand E c a η centers i p z
      ∂euclideanGaussianLaw E) := by
  apply continuous_of_dominated
  · intro p
    exact (observedComponentIntegrand_integrable E c a η centers i p).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (observedComponentIntegrand_bound E c a η centers i p)
  · exact gaussianExponentialDensity_integrable E (a⁻¹ • (centers i - c))
  · apply ae_of_all
    intro z
    unfold observedComponentIntegrand clip
    fun_prop

theorem observedClippedLoss_continuous (c : E) (a η : ℝ) (centers : ι → E) :
    Continuous (observedClippedLoss E c a η centers) := by
  apply continuous_finset_sum
  intro i _
  exact (observedComponentIntegral_continuous E c a η centers i).smul continuous_const

omit [BorelSpace E] in
theorem observedClippedLoss_apply (c : E) (a η : ℝ) (centers : ι → E)
    (p : E × (ι → ℝ)) (q : ι → ℝ) :
    observedClippedLoss E c a η centers p q =
      ∑ i, q i * ∫ z, observedComponentIntegrand E c a η centers i p z ∂euclideanGaussianLaw E := by
  simp [observedClippedLoss, mul_comm]

/-- The linear coefficient operator is the expectation under the actual physical mixture. -/
theorem observedClippedLoss_eq_expectation (c : E) (a η : ℝ) (centers : ι → E)
    (p : E × (ι → ℝ)) {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) :
    observedClippedLoss E c a η centers p q =
      ∫ u, clip (η * ⟪p.1, u - finiteMixtureMean centers p.2⟫_ℝ)
        ∂physicalGaussianMixtureLaw E c a centers q := by
  have hm : Measurable (fun u : E => clip (η * ⟪p.1, u - finiteMixtureMean centers p.2⟫_ℝ)) := by
    unfold clip
    fun_prop
  rw [physicalGaussianMixtureLaw,
    integral_map (f := fun u : E => clip (η * ⟪p.1, u - finiteMixtureMean centers p.2⟫_ℝ))
      (show Measurable (fun z : E => c + a • z) by fun_prop).aemeasurable hm.aestronglyMeasurable,
    integral_densityMeasure
      (w := mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) q)
      (mixtureDensity_measurable (fun i => (gaussianLogDensity_measurable E (a⁻¹ • (centers i - c))).exp) q)
      (fun z => (mixtureDensity_pos (fun _i _z => Real.exp_pos _) hq z).le)]
  simp_rw [mixtureDensity_eq_sum, Finset.sum_mul, mul_assoc]
  change _ = ∫ z, ∑ i, q i * observedComponentIntegrand E c a η centers i p z ∂euclideanGaussianLaw E
  rw [integral_finset_sum _ (fun i _ =>
    (observedComponentIntegrand_integrable E c a η centers i p).const_mul (q i))]
  simp only [integral_const_mul, observedClippedLoss_apply]

variable [Nonempty ι]

/-- The actual observation and current mixture determine a measurable approximate update. -/
theorem gaussian_observation_update_exists (c : E) (a η β : ℝ) (centers : ι → E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ update : E × SimplexPoint ι → SimplexPoint ι, Measurable update ∧
      ∀ p q, q ∈ stdSimplex ℝ ι →
        -ε ≤ (observedClippedLoss E c a η centers (p.1, p.2.val) +
          gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
            (finiteMixtureMean centers) (update p).val -
          gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
            (finiteMixtureMean centers) p.2.val) (q - (update p).val) := by
  obtain ⟨u, hu, hfirst⟩ := gaussian_measurable_first_order_update_exists E
    (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers) hε
  let input : E × SimplexPoint ι → ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι :=
    fun p => (observedClippedLoss E c a η centers (p.1, p.2.val), p.2)
  have hin : Measurable input :=
    (((observedClippedLoss_continuous E c a η centers).measurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))).prodMk measurable_snd)
  exact ⟨u ∘ input, hu.comp hin, fun p q hq => hfirst (input p) q hq⟩

end HeavyTail.GaussianEntropy
