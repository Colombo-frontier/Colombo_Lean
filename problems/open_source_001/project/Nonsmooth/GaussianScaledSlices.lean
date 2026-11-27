import Nonsmooth.ConditionalImage
import Nonsmooth.ConditionalReencoding
import Nonsmooth.RotationalConditionalMean

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem scaled_truncatedGaussian_projection_covariance (K : Submodule ℝ E)
    {c : ℝ} (hc : c ≠ 0) :
    ∀ᵐ x ∂((truncatedGaussianLaw E).map (fun z : E => c • z)).map
      (fun z : E => (K.orthogonalProjectionOnto z : E)),
      ∀ u : E, variance (fun z : E => ⟪u, z⟫_ℝ)
        (condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
          ((truncatedGaussianLaw E).map (fun z : E => c • z)) x) ≤ c ^ 2 * ‖u‖ ^ 2 := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjectionOnto
  let f : E → E := fun z => c • z
  let g : E → E := fun z => c⁻¹ • z
  have hf : Measurable f := measurable_const.smul measurable_id
  have hg : Measurable g := measurable_const.smul measurable_id
  have hZ : Measurable (P ∘ f) := P.measurable.comp hf
  have hZX (z : E) : (P ∘ f) z = f (P z) := P.map_smul c z
  have hXZ (z : E) : g ((P ∘ f) z) = P z := by
    rw [hZX]
    simp only [g, f, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hp := condDistrib_property_reencoding (truncatedGaussianLaw E)
    P P.measurable id measurable_id (P ∘ f) hZ f hf g hg hZX hXZ
    (fun ν : Measure E => ∀ u : E, variance (fun z : E => ⟪u, z⟫_ℝ) ν ≤ ‖u‖ ^ 2)
    (truncatedGaussian_projection_covariance K)
  have hm := condDistrib_map_prior (truncatedGaussianLaw E) f hf P P.measurable
  rw [Measure.map_map P.measurable hf] at hm
  change ∀ᵐ x ∂((truncatedGaussianLaw E).map f).map P,
    ∀ u : E, variance (fun z : E => ⟪u, z⟫_ℝ) (condDistrib id P ((truncatedGaussianLaw E).map f) x) ≤
      c ^ 2 * ‖u‖ ^ 2
  rw [Measure.map_map P.measurable hf]
  filter_upwards [hp, hm] with x hx he
  intro u
  have hi : Measurable (fun z : E => ⟪u, z⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  rw [he, variance_map_measurable _ f hf _ hi]
  have hfun : ((fun z : E => ⟪u, z⟫_ℝ) ∘ f) = fun z : E => c * ⟪u, z⟫_ℝ := by
    funext z
    simp only [Function.comp_def, f, real_inner_smul_right]
  rw [hfun, variance_const_mul]
  exact mul_le_mul_of_nonneg_left (hx u) (sq_nonneg c)

theorem gaussianAmbientRow_projection_covariance (K : Submodule ℝ E) :
    ∀ᵐ x ∂(gaussianAmbientRowLaw E).map (fun z : E => (K.orthogonalProjectionOnto z : E)),
      ∀ u : E, variance (fun z : E => ⟪u, z⟫_ℝ)
        (condDistrib id (fun z : E => (K.orthogonalProjectionOnto z : E))
          (gaussianAmbientRowLaw E) x) ≤ ‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hc : (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr hd).ne'
  have he := scaled_truncatedGaussian_projection_covariance K hc
  simp only [inv_pow, Real.sq_sqrt hd.le, ← div_eq_inv_mul] at he
  simpa only [gaussianAmbientRowLaw, gaussianSupportRowLaw_map] using he

theorem gaussianAmbientRow_scalar_covariance {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ y ∂(gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ),
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ)
        (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (gaussianAmbientRowLaw E) y) ≤
          ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let P : E →L[ℝ] E := (ℝ ∙ u).subtypeL.comp (ℝ ∙ u).orthogonalProjectionOnto
  let r : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hr : Measurable r := (continuous_id.inner continuous_const).measurable
  have hZX (z : E) : r z = r (P z) := by
    change ⟪z, u⟫_ℝ = ⟪((ℝ ∙ u).orthogonalProjectionOnto z : E), u⟫_ℝ
    rw [unit_orthogonalProjection_formula hu]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    ring
  have hXZ (z : E) : (r z) • u = P z := (unit_orthogonalProjection_formula hu z).symm
  exact condDistrib_property_reencoding (gaussianAmbientRowLaw E)
    P P.measurable id measurable_id r hr r hr (fun y : ℝ => y • u)
    (measurable_id.smul measurable_const) hZX hXZ
    (fun ν : Measure E => ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ)) (gaussianAmbientRow_projection_covariance (ℝ ∙ u))

end
end Nonsmooth
