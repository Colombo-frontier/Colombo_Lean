import HeavyTail.GaussianOnlineMaster

/-! Exact initial divergence for a comparator component and a central
Gaussian initialization, with no assumed KL estimate. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {ι Ω V : Type*} [Fintype ι] [DecidableEq ι]

theorem mixtureDensity_single_component (φ : ι → Ω → ℝ) (i : ι) :
    mixtureDensity φ (Pi.single i 1) = φ i := by
  classical
  funext z
  simp [mixtureDensity_eq_sum, Pi.single_apply]

theorem finiteMixtureMean_single_component [NormedAddCommGroup V] [NormedSpace ℝ V]
    (centers : ι → V) (i : ι) : finiteMixtureMean centers (Pi.single i 1) = centers i := by
  classical
  simp [finiteMixtureMean_apply, Pi.single_apply]

namespace GaussianEntropy
open GaussianEstimates

variable [Nonempty ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussianOnlineDivergence_initial_exact (c : E) (a β : ℝ)
    (centers : ι → E) (i i₀ : ι) (h₀ : centers i₀ = c) :
    gaussianOnlineDivergence E c a β centers (Pi.single i 1) (Pi.single i₀ 1) =
      ‖centers i - c‖ ^ 2 / (2 * a ^ 2) + β / 2 * ‖centers i - c‖ ^ 2 := by
  classical
  dsimp only [gaussianOnlineDivergence, gaussianOnlineGenerator, gaussianOnlineDerivative]
  rw [gaussian_mixture_generator_bregman E (fun i => a⁻¹ • (centers i - c)) β (finiteMixtureMean centers)
    (single_mem_stdSimplex ℝ i) (single_mem_stdSimplex ℝ i₀)]
  simp only [mixtureDensity_single_component, finiteMixtureMean_single_component, h₀,
    sub_self, smul_zero]
  have hzero : gaussianExponentialDensity E (0 : E) = fun _ => (1 : ℝ) := by
    funext z
    simp [gaussianExponentialDensity, gaussianLogDensity]
  rw [hzero, gaussian_comparator_KL E]

theorem gaussianOnlineDivergence_initial_bound (c : E) (a : ℝ) {β R : ℝ}
    (hβ : 0 ≤ β) (hR : 0 ≤ R) (centers : ι → E) (i i₀ : ι)
    (h₀ : centers i₀ = c) (hi : ‖centers i - c‖ ≤ R) :
    gaussianOnlineDivergence E c a β centers (Pi.single i 1) (Pi.single i₀ 1) ≤
      R ^ 2 / (2 * a ^ 2) + β / 2 * R ^ 2 := by
  rw [gaussianOnlineDivergence_initial_exact E c a β centers i i₀ h₀]
  have hs : ‖centers i - c‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (centers i - c)]
  exact add_le_add (div_le_div_of_nonneg_right hs (by positivity))
    (mul_le_mul_of_nonneg_left hs (by positivity))

end GaussianEntropy
end HeavyTail
