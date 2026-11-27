import Nonsmooth.RadialAveraging
import Nonsmooth.GaussianDirection
import Nonsmooth.GaussianConditionalMeans
import Nonsmooth.TruncationMonotonicity
import Nonsmooth.EventComplement

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem inner_cosh_integrable (μ : Measure E)
    (hI : ∀ u : E, Integrable (fun x => Real.exp ⟪u, x⟫_ℝ) μ) (u : E) :
    Integrable (fun x : E => Real.cosh ⟪u, x⟫_ℝ) μ := by
  simpa only [Real.cosh_eq, inner_neg_left, Pi.add_apply] using ((hI u).add (hI (-u))).div_const 2

theorem neg_invariant_exp_eq_cosh (μ : Measure E)
    (hneg : μ.map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) = μ)
    (hI : ∀ u : E, Integrable (fun x => Real.exp ⟪u, x⟫_ℝ) μ) (u : E) :
    (∫ x : E, Real.exp ⟪u, x⟫_ℝ ∂μ) = ∫ x : E, Real.cosh ⟪u, x⟫_ℝ ∂μ := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hp : MeasurePreserving e μ μ := ⟨e.continuous.measurable, hneg⟩
  have he := hp.integral_comp e.toMeasurableEquiv.measurableEmbedding
    (fun x : E => Real.exp ⟪u, x⟫_ℝ)
  change (∫ x : E, Real.exp ⟪u, -x⟫_ℝ ∂μ) = ∫ x : E, Real.exp ⟪u, x⟫_ℝ ∂μ at he
  simp only [inner_neg_right] at he
  have hiNeg : Integrable (fun x : E => Real.exp (-⟪u, x⟫_ℝ)) μ := by
    simpa only [inner_neg_left] using hI (-u)
  simp_rw [Real.cosh_eq]
  rw [integral_div, integral_add (hI u) hiNeg, he]
  ring

/-- Conditioning a rotational Gaussian on a centered ball cannot increase a linear exponential moment. -/
theorem truncatedGaussian_exp_inner_sharp (u : E) :
    (∫ z : E, Real.exp ⟪u, z⟫_ℝ ∂truncatedGaussianLaw E) ≤ Real.exp (‖u‖ ^ 2 / 2) := by
  let f : E → ℝ := fun z => Real.cosh ⟪u, z⟫_ℝ
  let R : ℝ := 2 * Real.sqrt (Module.finrank ℝ E)
  have hR : 0 ≤ R := by positivity
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hraw := rotational_radial_average (euclideanGaussianLaw E) euclideanGaussianLaw_nonzero
    euclideanGaussianLaw_isometry hf (inner_cosh_integrable _ euclideanGaussian_exp_inner_integrable u)
  have htr := rotational_radial_average (truncatedGaussianLaw E) truncatedGaussianLaw_nonzero
    truncatedGaussianLaw_isometry hf (inner_cosh_integrable _ truncatedGaussian_exp_inner_integrable u)
  have hbound : (∫ z : E, sphericalRadialAverage f ‖z‖ ∂truncatedGaussianLaw E) ≤
      ∫ z : E, sphericalRadialAverage f ‖z‖ ∂euclideanGaussianLaw E := by
    apply integral_event_le_of_separated hraw.1 measurableSet_closedBall
      euclideanGaussianLaw_truncation_positive.ne' (sphericalRadialAverage f R)
    · filter_upwards [ae_restrict_mem (μ := euclideanGaussianLaw E) measurableSet_closedBall] with z hz
      have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
      exact spherical_cosh_radial_mono u (norm_nonneg z) hz'
    · filter_upwards [ae_restrict_mem (μ := euclideanGaussianLaw E) measurableSet_closedBall.compl] with z hz
      have hz' : R ≤ ‖z‖ := le_of_lt (by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz)
      exact spherical_cosh_radial_mono u hR hz'
  calc
    _ = ∫ z : E, f z ∂truncatedGaussianLaw E := neg_invariant_exp_eq_cosh _
      (truncatedGaussianLaw_isometry (LinearIsometryEquiv.neg ℝ)) truncatedGaussian_exp_inner_integrable u
    _ = ∫ z : E, sphericalRadialAverage f ‖z‖ ∂truncatedGaussianLaw E := htr.2
    _ ≤ ∫ z : E, sphericalRadialAverage f ‖z‖ ∂euclideanGaussianLaw E := hbound
    _ = ∫ z : E, f z ∂euclideanGaussianLaw E := hraw.2.symm
    _ = ∫ z : E, Real.exp ⟪u, z⟫_ℝ ∂euclideanGaussianLaw E :=
      (neg_invariant_exp_eq_cosh _ (euclideanGaussianLaw_isometry (LinearIsometryEquiv.neg ℝ))
        euclideanGaussian_exp_inner_integrable u).symm
    _ = _ := euclideanGaussian_exp_inner u

theorem gaussianAmbientRow_exp_inner_sharp (u : E) :
    (∫ a : E, Real.exp ⟪u, a⟫_ℝ ∂gaussianAmbientRowLaw E) ≤
      Real.exp ((Module.finrank ℝ E : ℝ)⁻¹ * ‖u‖ ^ 2 / 2) := by
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  have hf : StronglyMeasurable (fun z : E => Real.exp ⟪u, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).rexp.stronglyMeasurable
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map, integral_map_of_stronglyMeasurable hm hf]
  have he (z : E) : ⟪u, (Real.sqrt (Module.finrank ℝ E))⁻¹ • z⟫_ℝ =
      ⟪(Real.sqrt (Module.finrank ℝ E))⁻¹ • u, z⟫_ℝ := by
    simp only [inner_smul_right, real_inner_smul_left]
  simp_rw [he]
  have h := truncatedGaussian_exp_inner_sharp ((Real.sqrt (Module.finrank ℝ E))⁻¹ • u)
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hd.le] using h

theorem gaussianAmbientRow_event_mean_sharp (A : Set E) (hA : gaussianAmbientRowLaw E A ≠ 0) :
    ‖∫ a : E, a ∂(gaussianAmbientRowLaw E)[|A]‖ ^ 2 ≤
      (2 / (Module.finrank ℝ E : ℝ)) * Real.log (1 / (gaussianAmbientRowLaw E).real A) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have h := event_barycenter_of_exp_moments
    ((gaussianAmbientRowLaw_memLp (E := E)).integrable (by norm_num))
    (inv_pos.mpr hd) (by norm_num : (0 : ℝ) < 1) gaussianAmbientRow_exp_inner_integrable
    (fun u => by simpa only [one_mul] using gaussianAmbientRow_exp_inner_sharp u) A hA
  simpa only [div_eq_mul_inv] using h

theorem gaussianAmbientRow_event_mean_two_sided {A : Set E} (hAm : MeasurableSet A)
    (hA : gaussianAmbientRowLaw E A ≠ 0) (hAc : gaussianAmbientRowLaw E Aᶜ ≠ 0) :
    ‖∫ a : E, a ∂(gaussianAmbientRowLaw E)[|A]‖ ^ 2 ≤
      min ((2 / (Module.finrank ℝ E : ℝ)) * Real.log (1 / (gaussianAmbientRowLaw E).real A))
        (((gaussianAmbientRowLaw E).real Aᶜ / (gaussianAmbientRowLaw E).real A) ^ 2 *
          ((2 / (Module.finrank ℝ E : ℝ)) * Real.log (1 / (gaussianAmbientRowLaw E).real Aᶜ))) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have h := event_barycenter_two_sided
    ((gaussianAmbientRowLaw_memLp (E := E)).integrable (by norm_num)) gaussianAmbientRowLaw_mean_zero
    (inv_pos.mpr hd) (by norm_num : (0 : ℝ) < 1) gaussianAmbientRow_exp_inner_integrable
    (fun u => by simpa only [one_mul] using gaussianAmbientRow_exp_inner_sharp u) hAm hA hAc
  simpa only [div_eq_mul_inv] using h

end
end Nonsmooth
