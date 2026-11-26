import HeavyTail.GaussianExactUpdate
import HeavyTail.GaussianMeasurableUpdateLoss

/-! Exact measurable minimization of the manuscript's actual clipped Gaussian
loss plus KL and quadratic mean penalty. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace HeavyTail.GaussianEntropy

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_clipped_observation_exact_optimizer_exists
    (c : E) (a η : ℝ) {β : ℝ} (hβ : 0 ≤ β) (centers : ι → E) :
    ∃ update : E × SimplexPoint ι → SimplexPoint ι, Measurable update ∧
      ∀ p, IsMinOn
        (fun z => observedClippedLoss E c a η centers (p.1, p.2.val) z +
          bregmanDivergence
            (gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
            (gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
              (finiteMixtureMean centers)) z p.2.val)
        (stdSimplex ℝ ι) (update p).val := by
  obtain ⟨u, hu, hmin⟩ := gaussian_measurable_exact_optimizer_exists E
    (fun i => a⁻¹ • (centers i - c)) hβ (finiteMixtureMean centers)
  let input : E × SimplexPoint ι → ((ι → ℝ) →L[ℝ] ℝ) × SimplexPoint ι :=
    fun p => (observedClippedLoss E c a η centers (p.1, p.2.val), p.2)
  have hin : Measurable input :=
    (((observedClippedLoss_continuous E c a η centers).measurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))).prodMk measurable_snd)
  exact ⟨u ∘ input, hu.comp hin, fun p => hmin (input p)⟩

theorem gaussian_clipped_observation_exact_first_order_exists
    (c : E) (a η : ℝ) {β : ℝ} (hβ : 0 ≤ β) (centers : ι → E) :
    ∃ update : E × SimplexPoint ι → SimplexPoint ι, Measurable update ∧
      ∀ p q, q ∈ stdSimplex ℝ ι →
        0 ≤ (observedClippedLoss E c a η centers (p.1, p.2.val) +
          gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
            (finiteMixtureMean centers) (update p).val -
          gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
            (finiteMixtureMean centers) p.2.val) (q - (update p).val) := by
  obtain ⟨u, hu, hmin⟩ := gaussian_clipped_observation_exact_optimizer_exists E c a η hβ centers
  refine ⟨u, hu, ?_⟩
  intro p q hq
  exact constrained_minimum_first_order (convex_stdSimplex ℝ ι) (u p).property hq (hmin p)
    (mirror_objective_derivative (observedClippedLoss E c a η centers (p.1, p.2.val))
      (gaussian_mixture_generator_derivative E (fun i => a⁻¹ • (centers i - c)) β
        (finiteMixtureMean centers) (u p).property))

/-- Literal source objective: expected clipped loss under the actual physical
Gaussian mixture, Gaussian density KL, and quadratic change in mixture mean. -/
theorem gaussian_clipped_observation_exact_KL_optimizer_exists
    (c : E) (a η : ℝ) {β : ℝ} (hβ : 0 ≤ β) (centers : ι → E) :
    ∃ update : E × SimplexPoint ι → SimplexPoint ι, Measurable update ∧
      ∀ p, IsMinOn
        (fun z => (∫ u, clip (η * ⟪p.1, u - finiteMixtureMean centers p.2.val⟫_ℝ)
          ∂physicalGaussianMixtureLaw E c a centers z) +
          densityRelativeEntropy (GaussianEstimates.euclideanGaussianLaw E)
            (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) z)
            (mixtureDensity (fun i => gaussianExponentialDensity E (a⁻¹ • (centers i - c))) p.2.val) +
          β / 2 * ‖finiteMixtureMean centers z - finiteMixtureMean centers p.2.val‖ ^ 2)
        (stdSimplex ℝ ι) (update p).val := by
  obtain ⟨u, hu, hmin⟩ := gaussian_clipped_observation_exact_optimizer_exists E c a η hβ centers
  refine ⟨u, hu, ?_⟩
  intro p z hz
  have h := hmin p hz
  change observedClippedLoss E c a η centers (p.1, p.2.val) (u p).val +
      bregmanDivergence
        (gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
        (gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
          (finiteMixtureMean centers)) (u p).val p.2.val ≤
    observedClippedLoss E c a η centers (p.1, p.2.val) z +
      bregmanDivergence
        (gaussianMixtureGenerator E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers))
        (gaussianMixtureGeneratorDerivative E (fun i => a⁻¹ • (centers i - c)) β
          (finiteMixtureMean centers)) z p.2.val at h
  rw [gaussian_mixture_generator_bregman E _ β _ (u p).property p.2.property,
    gaussian_mixture_generator_bregman E _ β _ hz p.2.property,
    observedClippedLoss_eq_expectation E c a η centers _ (u p).property,
    observedClippedLoss_eq_expectation E c a η centers _ hz] at h
  simpa only [add_assoc] using h

end HeavyTail.GaussianEntropy
