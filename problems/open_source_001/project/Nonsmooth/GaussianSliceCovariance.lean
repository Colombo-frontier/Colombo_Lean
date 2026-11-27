import Nonsmooth.GaussianSubspaceLaw
import Nonsmooth.GaussianRadialTruncation

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussian_residual_radial_condition (K : Submodule ℝ E) [Nontrivial Kᗮ] (t : ℝ) :
    (gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}] =
      ((euclideanGaussianLaw Kᗮ)[|{z : Kᗮ | ‖z‖ ^ 2 ≤ t}]).map Kᗮ.subtype := by
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  rw [gaussianOrthogonalResidualLaw_subspace,
    conditioning_map_preimage _ _ hsub {z : E | ‖z‖ ^ 2 ≤ t}
      (measurableSet_le (show Measurable (fun z : E => ‖z‖ ^ 2) from by fun_prop) measurable_const)]
  rfl

theorem gaussian_residual_radial_directional_second (K : Submodule ℝ E) [Nontrivial Kᗮ]
    (t : ℝ) (hpos : gaussianOrthogonalResidualLaw K {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) (u : E) :
    (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂(gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}]) ≤
      ‖u‖ ^ 2 := by
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  have hA : MeasurableSet {z : E | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (continuous_norm.pow 2).measurable measurable_const
  rw [gaussianOrthogonalResidualLaw_subspace, Measure.map_apply hsub hA] at hpos
  have hp : euclideanGaussianLaw Kᗮ {z : Kᗮ | ‖z‖ ^ 2 ≤ t} ≠ 0 := hpos
  have hf : StronglyMeasurable (fun z : E => ⟪u, z⟫_ℝ ^ 2) :=
    ((continuous_const.inner continuous_id).pow 2).stronglyMeasurable
  rw [gaussian_residual_radial_condition, integral_map_of_stronglyMeasurable hsub hf]
  change (∫ z : Kᗮ, ⟪u, (z : E)⟫_ℝ ^ 2 ∂
    (euclideanGaussianLaw Kᗮ)[|{z : Kᗮ | ‖z‖ ^ 2 ≤ t}]) ≤ ‖u‖ ^ 2
  have hi (z : Kᗮ) : ⟪u, (z : E)⟫_ℝ = ⟪Kᗮ.orthogonalProjectionOnto u, z⟫_ℝ :=
    (Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_right z u).symm
  simp_rw [hi]
  apply (gaussian_radial_threshold_directional_second t hp (Kᗮ.orthogonalProjectionOnto u)).trans
  have he := orthogonal_components_energy Kᗮ u
  change ‖(Kᗮ.orthogonalProjectionOnto u : E)‖ ^ 2 ≤ ‖u‖ ^ 2
  nlinarith [sq_nonneg ‖u - (Kᗮ.orthogonalProjectionOnto u : E)‖]

theorem gaussian_residual_radial_mean_zero (K : Submodule ℝ E) [Nontrivial Kᗮ]
    (t : ℝ) (hpos : gaussianOrthogonalResidualLaw K {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) :
    (∫ z : E, z ∂(gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}]) = 0 := by
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  have hA : MeasurableSet {z : E | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (continuous_norm.pow 2).measurable measurable_const
  rw [gaussianOrthogonalResidualLaw_subspace, Measure.map_apply hsub hA] at hpos
  have hp : euclideanGaussianLaw Kᗮ {z : Kᗮ | ‖z‖ ^ 2 ≤ t} ≠ 0 := hpos
  have hid : StronglyMeasurable (fun z : E => z) := stronglyMeasurable_id
  rw [gaussian_residual_radial_condition,
    integral_map_of_stronglyMeasurable hsub hid]
  change (∫ z : Kᗮ, Kᗮ.subtypeL z ∂(euclideanGaussianLaw Kᗮ)[|{z : Kᗮ | ‖z‖ ^ 2 ≤ t}]) = 0
  rw [Kᗮ.subtypeL.integral_comp_comm ((gaussian_radial_threshold_memLp t hp).integrable (by norm_num)),
    gaussian_radial_threshold_mean_zero, map_zero]

theorem gaussian_residual_radial_directional_second_all (K : Submodule ℝ E)
    (t : ℝ) (hpos : gaussianOrthogonalResidualLaw K {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) (u : E) :
    (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂(gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}]) ≤
      ‖u‖ ^ 2 := by
  rcases subsingleton_or_nontrivial Kᗮ with hK | hK
  · letI := hK
    have hz : ∀ᵐ z ∂gaussianOrthogonalResidualLaw K, z = 0 := by
      filter_upwards [gaussianOrthogonalResidualLaw_supported K] with z hz
      exact congrArg (fun w : Kᗮ => (w : E)) (Subsingleton.elim ⟨z, hz⟩ 0)
    have hc : ∀ᵐ z ∂(gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}], z = 0 :=
      Measure.ae_smul_measure (ae_restrict_of_ae hz) _
    have he : (∫ z : E, ⟪u, z⟫_ℝ ^ 2 ∂
        (gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}]) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hc] with z hz
      simp [hz]
    rw [he]
    exact sq_nonneg ‖u‖
  · letI := hK
    exact gaussian_residual_radial_directional_second K t hpos u

theorem gaussian_residual_radial_memLp (K : Submodule ℝ E) (t : ℝ)
    (hpos : gaussianOrthogonalResidualLaw K {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) :
    MemLp (fun z : E => z) 2 (gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}] := by
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - K.subtypeL.comp K.orthogonalProjectionOnto
  have hraw : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  have hres : MemLp (fun z : E => z) 2 (gaussianOrthogonalResidualLaw K) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable R.measurable.aemeasurable).mpr
      (R.comp_memLp' hraw)
  exact (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
    (integrable_under_event hres.norm.integrable_sq hpos)

theorem gaussian_residual_radial_mean_zero_all (K : Submodule ℝ E) (t : ℝ)
    (hpos : gaussianOrthogonalResidualLaw K {z : E | ‖z‖ ^ 2 ≤ t} ≠ 0) :
    (∫ z : E, z ∂(gaussianOrthogonalResidualLaw K)[|{z : E | ‖z‖ ^ 2 ≤ t}]) = 0 := by
  rcases subsingleton_or_nontrivial Kᗮ with hK | hK
  · letI := hK
    have hz : ∀ᵐ z ∂gaussianOrthogonalResidualLaw K, z = 0 := by
      filter_upwards [gaussianOrthogonalResidualLaw_supported K] with z hz
      exact congrArg (fun w : Kᗮ => (w : E)) (Subsingleton.elim ⟨z, hz⟩ 0)
    apply integral_eq_zero_of_ae
    exact Measure.ae_smul_measure (ae_restrict_of_ae hz) _
  · letI := hK
    exact gaussian_residual_radial_mean_zero K t hpos

theorem truncatedGaussian_projection_mean (K : Submodule ℝ E) :
    ∀ᵐ x ∂(truncatedGaussianLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      (∫ z : E, z ∂condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
        (truncatedGaussianLaw E) x) = x := by
  filter_upwards [truncatedGaussian_projection_posterior K] with x hx
  rw [hx.1]
  have hid : StronglyMeasurable (fun z : E => z) := stronglyMeasurable_id
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hid]
  letI := cond_isProbabilityMeasure hx.2
  rw [integral_add (integrable_const x)
      ((gaussian_residual_radial_memLp K _ hx.2).integrable (by norm_num)),
    integral_const, gaussian_residual_radial_mean_zero_all K _ hx.2]
  simp

/-- Sharp conditional directional bound for the actual ball-truncated Gaussian
after observing any fixed subspace, including the full subspace. -/
theorem truncatedGaussian_projection_centered_second (K : Submodule ℝ E) :
    ∀ᵐ x ∂(truncatedGaussianLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      ∀ u : E, (∫ z : E, ⟪u, z - x⟫_ℝ ^ 2 ∂
        condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E)) (truncatedGaussianLaw E) x) ≤
          ‖u‖ ^ 2 := by
  filter_upwards [truncatedGaussian_projection_posterior K] with x hx
  intro u
  rw [hx.1]
  have hf : StronglyMeasurable (fun z : E => ⟪u, z - x⟫_ℝ ^ 2) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hf]
  simp only [add_sub_cancel_left]
  exact gaussian_residual_radial_directional_second_all K _ hx.2 u

theorem truncatedGaussian_projection_covariance (K : Submodule ℝ E) :
    ∀ᵐ x ∂(truncatedGaussianLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      ∀ u : E, variance (fun z : E => ⟪u, z⟫_ℝ)
        (condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
          (truncatedGaussianLaw E) x) ≤ ‖u‖ ^ 2 := by
  have hb : ∀ᵐ x ∂(truncatedGaussianLaw E).map
      (fun z : E => (K.orthogonalProjectionOnto z : E)),
      ∀ᵐ z ∂condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
        (truncatedGaussianLaw E) x, ‖z‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E) := by
    let X : E → E := fun z => (K.orthogonalProjectionOnto z : E)
    have hX : Measurable X := (K.subtypeL.comp K.orthogonalProjectionOnto).measurable
    have hpair : Measurable (fun z : E => (X z, z)) := hX.prodMk measurable_id
    have hs : MeasurableSet {p : E × E | ‖p.2‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E)} :=
      measurableSet_le continuous_snd.norm.measurable measurable_const
    have hj : ∀ᵐ p ∂(truncatedGaussianLaw E).map (fun z => (X z, z)),
        ‖p.2‖ ≤ 2 * Real.sqrt (Module.finrank ℝ E) :=
      (ae_map_iff hpair.aemeasurable hs).mpr truncatedGaussianLaw_supported
    have he := compProd_map_condDistrib (X := X) (μ := truncatedGaussianLaw E) (mβ := inferInstance) aemeasurable_id
    simp only [id_eq] at he
    rw [← he] at hj
    exact Measure.ae_ae_of_ae_compProd hj
  filter_upwards [truncatedGaussian_projection_centered_second K,
    truncatedGaussian_projection_mean K, hb] with x hsecond hmean hbound
  intro u
  have hV : MemLp (fun z : E => z) 2
      (condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E)) (truncatedGaussianLaw E) x) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable _ hbound
  rw [variance_eq_integral (hV.const_inner u).aestronglyMeasurable.aemeasurable,
    integral_inner (hV.integrable (by norm_num)), hmean]
  simpa only [inner_sub_right] using hsecond u

end
end Nonsmooth
