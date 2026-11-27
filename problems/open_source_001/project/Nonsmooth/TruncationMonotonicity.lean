import Nonsmooth.EventBarycenter
import Nonsmooth.GaussianEnergy

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

/-- Conditioning on the lower part of an integrable random variable decreases its expectation. -/
theorem integral_event_le_of_separated {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    {A : Set α} (hAm : MeasurableSet A) (hA : μ A ≠ 0) (c : ℝ)
    (hlo : ∀ᵐ x ∂μ.restrict A, f x ≤ c) (hhi : ∀ᵐ x ∂μ.restrict Aᶜ, c ≤ f x) :
    (∫ x, f x ∂μ[|A]) ≤ ∫ x, f x ∂μ := by
  have h1 := integral_mono_ae hf.restrict (integrable_const c) hlo
  have h2 := integral_mono_ae (integrable_const c) hf.restrict hhi
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at h1 h2
  change (∫ x in A, f x ∂μ) ≤ μ.real A * c at h1
  change μ.real Aᶜ * c ≤ (∫ x in Aᶜ, f x ∂μ) at h2
  have hp : 0 < μ.real A := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hq : 0 ≤ μ.real Aᶜ := measureReal_nonneg
  have he : μ.real A + μ.real Aᶜ = 1 := by
    rw [measureReal_compl hAm]
    simp
  have h1' := mul_le_mul_of_nonneg_left h1 hq
  have h2' := mul_le_mul_of_nonneg_left h2 hp.le
  have hqeq : μ.real Aᶜ = 1 - μ.real A := by linarith
  rw [hqeq] at h1' h2'
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change (μ.real A)⁻¹ * (∫ x in A, f x ∂μ) ≤ _
  rw [← div_eq_inv_mul, div_le_iff₀ hp, ← integral_add_compl hAm hf]
  nlinarith only [h1', h2']

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussian_ball_conditioned_norm_second_le {R : ℝ} (hR : 0 ≤ R)
    (hpos : euclideanGaussianLaw E (closedBall (0 : E) R) ≠ 0) :
    (∫ z : E, ‖z‖ ^ 2 ∂(euclideanGaussianLaw E)[|closedBall (0 : E) R]) ≤
      (Module.finrank ℝ E : ℝ) := by
  rw [← euclideanGaussian_norm_second_moment (E := E)]
  apply integral_event_le_of_separated euclideanGaussian_norm_square_integrable
    measurableSet_closedBall hpos (R ^ 2)
  · filter_upwards [ae_restrict_mem (μ := euclideanGaussianLaw E) measurableSet_closedBall] with z hz
    have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  · filter_upwards [ae_restrict_mem (μ := euclideanGaussianLaw E) measurableSet_closedBall.compl] with z hz
    have hz' : R < ‖z‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    nlinarith

theorem truncatedGaussian_norm_second_le :
    (∫ z : E, ‖z‖ ^ 2 ∂truncatedGaussianLaw E) ≤ (Module.finrank ℝ E : ℝ) :=
  gaussian_ball_conditioned_norm_second_le (by positivity) euclideanGaussianLaw_truncation_positive.ne'

end
end Nonsmooth
