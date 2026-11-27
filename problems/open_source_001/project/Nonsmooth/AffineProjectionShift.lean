import Nonsmooth.AffineObservationPosterior
import Nonsmooth.SupportWinnerRank

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] [Nontrivial F]

theorem affine_isometry_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (L : E →ₗᵢ[ℝ] F) (s : ℝ) (o : F) :
    (∫ z : F, z ∂μ.map (fun z => o + s • L z)) = o + s • L (∫ z : E, z ∂μ) := by
  have hf : Measurable (fun z : E => o + s • L z) := by fun_prop
  rw [integral_map_of_stronglyMeasurable hf
    (show StronglyMeasurable (fun z : F => z) from stronglyMeasurable_id)]
  have hiL : Integrable (fun z : E => s • L z) μ :=
    (L.toContinuousLinearMap.integrable_comp hi).smul s
  rw [integral_add (integrable_const _) hiL]
  rw [integral_const, integral_smul, L.integral_comp_comm]
  simp only [measureReal_univ_eq_one, one_smul]

/-- The actual centered projection posterior commutes with an affine isometric
state map and an invertible affine scalar observation. -/
theorem affine_isometry_projection_shift (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (L : E →ₗᵢ[ℝ] F) (s : ℝ) (o : F)
    (u : E) (q : F) {c : ℝ} (hc : c ≠ 0) (a : ℝ)
    (hobs : ∀ z : E, ⟪o + s • L z, q⟫_ℝ = a + c * ⟪z, u⟫_ℝ) :
    let ν := μ.map (fun z => o + s • L z)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
    ∀ᵐ y ∂ν.map (fun z : F => ⟪z, q⟫_ℝ),
      projectionPosteriorShift ν q y =
        s • L (projectionPosteriorShift μ u ((y - a) / c)) := by
  let f : E → F := fun z => o + s • L z
  have hf : Measurable f := by fun_prop
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hp := affine_observation_posterior μ f hf (fun z => ⟪z, u⟫_ℝ)
    (by fun_prop) (fun z : F => ⟪z, q⟫_ℝ) (by fun_prop) hc a hobs
  filter_upwards [hp] with y hy
  unfold projectionPosteriorShift
  rw [hy]
  rw [integral_map_of_stronglyMeasurable hf
    (show StronglyMeasurable (fun z : F => z - ∫ z : F, z ∂μ.map f) from
      stronglyMeasurable_id.sub stronglyMeasurable_const)]
  have hm := affine_isometry_mean μ hi L s o
  change (∫ z : E, (f z - ∫ z : F, z ∂μ.map f)
    ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ ((y - a) / c)) = _
  rw [hm]
  have he (z : E) : f z - (o + s • L (∫ z : E, z ∂μ)) =
      s • L (z - ∫ z : E, z ∂μ) := by
    simp only [f, map_sub, smul_sub]
    abel
  simp_rw [he]
  rw [integral_smul, L.integral_comp_comm]

end
end Nonsmooth
