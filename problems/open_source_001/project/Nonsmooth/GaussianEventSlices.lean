import Nonsmooth.ConditionalEventBayes

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem conditioning_map_preimage {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (A : Set β) (hA : MeasurableSet A) :
    (μ.map f)[|A] = (μ[|f ⁻¹' A]).map f := by
  simp only [ProbabilityTheory.cond, Measure.map_smul]
  rw [Measure.map_apply hf hA, Measure.restrict_map hf hA]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A Gaussian conditioned on any measurable event has affine Gaussian projection
slices conditioned on the same event, at almost every observed projection. -/
theorem gaussian_event_projection_posterior (K : Submodule ℝ E)
    (A : Set E) (hA : MeasurableSet A) :
    ∀ᵐ x ∂((euclideanGaussianLaw E)[|A]).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
        ((euclideanGaussianLaw E)[|A]) x =
          ((gaussianOrthogonalResidualLaw K)[|(fun z => x + z) ⁻¹' A]).map (fun z => x + z) ∧
        gaussianOrthogonalResidualLaw K ((fun z => x + z) ⁻¹' A) ≠ 0 := by
  have he := event_conditioned_posterior (euclideanGaussianLaw E)
    (fun z : E => (K.orthogonalProjectionOnto z : E))
    (K.subtypeL.comp K.orthogonalProjectionOnto).measurable (gaussianProjectionKernel K)
    (gaussianProjectionKernel_disintegrates K) A hA
  filter_upwards [he] with x hx
  rw [gaussianProjectionKernel_apply] at hx
  rw [conditioning_map_preimage _ _ (by fun_prop) A hA] at hx
  rw [Measure.map_apply (by fun_prop) hA] at hx
  exact hx

theorem gaussianOrthogonalResidualLaw_supported (K : Submodule ℝ E) :
    ∀ᵐ z ∂gaussianOrthogonalResidualLaw K, z ∈ Kᗮ := by
  unfold gaussianOrthogonalResidualLaw
  have hr : Measurable (fun z : E => z - (K.orthogonalProjectionOnto z : E)) :=
    measurable_id.sub (K.subtypeL.comp K.orthogonalProjectionOnto).measurable
  exact (ae_map_iff hr.aemeasurable Kᗮ.closed_of_finiteDimensional.measurableSet).mpr
    (Eventually.of_forall (fun z => K.sub_starProjection_mem_orthogonal z))

/-- On an affine orthogonal slice, ball truncation is a radial truncation of the
remaining Gaussian component. The threshold is allowed to be nonpositive. -/
theorem gaussian_slice_ball_radial (K : Submodule ℝ E) {x : E} (hx : x ∈ K)
    {r : ℝ} (hr : 0 ≤ r) :
    ((fun z : E => x + z) ⁻¹' closedBall (0 : E) r) =ᵐ[gaussianOrthogonalResidualLaw K]
      {z : E | ‖z‖ ^ 2 ≤ r ^ 2 - ‖x‖ ^ 2} := by
  filter_upwards [gaussianOrthogonalResidualLaw_supported K] with z hz
  apply propext
  have hi : ⟪x, z⟫_ℝ = 0 := (Submodule.mem_orthogonal _ _).mp hz x hx
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x z hi
  change x + z ∈ closedBall (0 : E) r ↔ ‖z‖ ^ 2 ≤ r ^ 2 - ‖x‖ ^ 2
  simp only [mem_closedBall, dist_zero_right]
  constructor <;> intro h
  · nlinarith [norm_nonneg (x + z)]
  · nlinarith [norm_nonneg (x + z)]

theorem truncatedGaussian_projection_posterior (K : Submodule ℝ E) :
    ∀ᵐ x ∂(truncatedGaussianLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E)) (truncatedGaussianLaw E) x =
        ((gaussianOrthogonalResidualLaw K)[|
          {z : E | ‖z‖ ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) - ‖x‖ ^ 2}]).map
          (fun z => x + z) ∧
      gaussianOrthogonalResidualLaw K
        {z : E | ‖z‖ ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) - ‖x‖ ^ 2} ≠ 0 := by
  have he := gaussian_event_projection_posterior K
    (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) measurableSet_closedBall
  have hmem : ∀ᵐ x ∂(truncatedGaussianLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      x ∈ K := by
    exact (ae_map_iff (K.subtypeL.comp K.orthogonalProjectionOnto).measurable.aemeasurable
      K.closed_of_finiteDimensional.measurableSet).mpr
        (Eventually.of_forall (fun z => (K.orthogonalProjectionOnto z).property))
  filter_upwards [he, hmem] with x hx hK
  have hrad := gaussian_slice_ball_radial K hK
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg (Module.finrank ℝ E)))
  have hsquare : (2 * Real.sqrt (Module.finrank ℝ E : ℝ)) ^ 2 =
      4 * (Module.finrank ℝ E : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num
  rw [hsquare] at hrad
  have hc : (gaussianOrthogonalResidualLaw K)[|
      (fun z => x + z) ⁻¹' closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))] =
      (gaussianOrthogonalResidualLaw K)[|
        {z : E | ‖z‖ ^ 2 ≤ 4 * (Module.finrank ℝ E : ℝ) - ‖x‖ ^ 2}] := by
    simp only [ProbabilityTheory.cond, measure_congr hrad, Measure.restrict_congr_set hrad]
  rw [hc, measure_congr hrad] at hx
  exact hx

end
end Nonsmooth
