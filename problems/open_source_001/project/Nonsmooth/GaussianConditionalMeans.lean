import Nonsmooth.GaussianLinearMGF
import Nonsmooth.EventBarycenter
import Nonsmooth.GaussianSupportPosterior

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_vector_integrable : Integrable (fun z : E => z) (euclideanGaussianLaw E) := by
  have hV : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  exact hV.integrable (by norm_num)

theorem euclideanGaussian_event_mean (A : Set E) (hA : euclideanGaussianLaw E A ≠ 0) :
    ‖∫ z : E, z ∂(euclideanGaussianLaw E)[|A]‖ ^ 2 ≤
      2 * Real.log (1 / (euclideanGaussianLaw E).real A) := by
  have h := event_barycenter_of_exp_moments (euclideanGaussian_vector_integrable (E := E))
    (v := 1) (K := 1) (by norm_num) (by norm_num)
    euclideanGaussian_exp_inner_integrable
    (fun u => by simp [euclideanGaussian_exp_inner]) A hA
  simpa using h

theorem truncatedGaussian_exp_inner_integrable (u : E) :
    Integrable (fun z : E => Real.exp ⟪u, z⟫_ℝ) (truncatedGaussianLaw E) :=
  integrable_under_event (euclideanGaussian_exp_inner_integrable u)
    euclideanGaussianLaw_truncation_positive.ne'

theorem truncatedGaussian_exp_inner_le (u : E) :
    (∫ z : E, Real.exp ⟪u, z⟫_ℝ ∂truncatedGaussianLaw E) ≤
      (4 / 3) * Real.exp (‖u‖ ^ 2 / 2) := by
  have h := integral_event_le (euclideanGaussian_exp_inner_integrable u)
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)))
  rw [euclideanGaussian_exp_inner] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hp := euclideanGaussian_truncation_probability (E := E)
  have hp0 : 0 < (euclideanGaussianLaw E).real
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by linarith
  rw [inv_eq_one_div, div_le_iff₀ hp0]
  linarith

theorem gaussianAmbientRow_exp_inner_integrable (u : E) :
    Integrable (fun a : E => Real.exp ⟪u, a⟫_ℝ) (gaussianAmbientRowLaw E) := by
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map]
  apply (integrable_map_measure
    ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable)
    (measurable_const.smul measurable_id).aemeasurable).mpr
  convert! (truncatedGaussian_exp_inner_integrable
    ((Real.sqrt (Module.finrank ℝ E))⁻¹ • u)) using 1
  funext z
  change Real.exp ⟪u, (Real.sqrt (Module.finrank ℝ E))⁻¹ • z⟫_ℝ = _
  simp only [inner_smul_right, real_inner_smul_left]

theorem gaussianAmbientRow_exp_inner_le (u : E) :
    (∫ a : E, Real.exp ⟪u, a⟫_ℝ ∂gaussianAmbientRowLaw E) ≤
      (4 / 3) * Real.exp ((Module.finrank ℝ E : ℝ)⁻¹ * ‖u‖ ^ 2 / 2) := by
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  have hf : StronglyMeasurable (fun z : E => Real.exp ⟪u, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).rexp.stronglyMeasurable
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map,
    integral_map_of_stronglyMeasurable hm hf]
  have he (z : E) : ⟪u, (Real.sqrt (Module.finrank ℝ E))⁻¹ • z⟫_ℝ =
      ⟪(Real.sqrt (Module.finrank ℝ E))⁻¹ • u, z⟫_ℝ := by
    simp only [inner_smul_right, real_inner_smul_left]
  simp_rw [he]
  have h := truncatedGaussian_exp_inner_le ((Real.sqrt (Module.finrank ℝ E))⁻¹ • u)
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hd)),
    mul_pow, inv_pow, Real.sq_sqrt hd.le] using h

/-- An unconditional event estimate for the actual scaled, ball-truncated manuscript row law. -/
theorem gaussianAmbientRow_event_mean (A : Set E) (hA : gaussianAmbientRowLaw E A ≠ 0) :
    ‖∫ a : E, a ∂(gaussianAmbientRowLaw E)[|A]‖ ^ 2 ≤
      (2 / (Module.finrank ℝ E : ℝ)) * Real.log ((4 / 3) / (gaussianAmbientRowLaw E).real A) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have h := event_barycenter_of_exp_moments
    ((gaussianAmbientRowLaw_memLp (E := E)).integrable (by norm_num))
    (inv_pos.mpr hd) (by norm_num : (0 : ℝ) < 4 / 3)
    gaussianAmbientRow_exp_inner_integrable gaussianAmbientRow_exp_inner_le A hA
  simpa only [div_eq_mul_inv] using h

end
end Nonsmooth
