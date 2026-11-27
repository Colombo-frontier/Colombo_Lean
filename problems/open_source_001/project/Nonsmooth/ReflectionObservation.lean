import Nonsmooth.RotationalConditionalMean
import Nonsmooth.DirectionalResidual

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {α β E : Type} [mα : MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem reflection_observation_setIntegral (μ : Measure α) (e : α ≃ᵐ α)
    (he : MeasurePreserving e μ μ) (F : α → β) (hF : Measurable F)
    (hfix : ∀ x, F (e x) = F x) (V : α → E) (hV : Integrable V μ)
    (K : Submodule ℝ E) (htransform : ∀ x, V (e x) = K.reflection (V x))
    {s : Set α} (hs : MeasurableSet[MeasurableSpace.comap F inferInstance] s) :
    (∫ x in s, (K.orthogonalProjection (V x) : E) ∂μ) = ∫ x in s, V x ∂μ := by
  have hsm := hF.comap_le s hs
  have hpre : e ⁻¹' s = s := by
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    ext x
    change F (e x) ∈ t ↔ F x ∈ t
    rw [hfix]
  have hfun : (fun x => s.indicator V (e x)) =
      s.indicator (fun x => K.reflection (V x)) := by
    funext x
    have hx : e x ∈ s ↔ x ∈ s := by
      change x ∈ e ⁻¹' s ↔ x ∈ s
      rw [hpre]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem (hx.mpr hxs), htransform]
    · rw [Set.indicator_of_notMem hxs,
        Set.indicator_of_notMem (fun h => hxs (hx.mp h))]
  have h := he.integral_comp e.measurableEmbedding (s.indicator V)
  rw [hfun, integral_indicator hsm, integral_indicator hsm] at h
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  have hP : Integrable (fun x => (K.orthogonalProjection (V x) : E)) μ := P.integrable_comp hV
  have hPP : Integrable (fun x => (K.orthogonalProjection (V x) : E) +
      (K.orthogonalProjection (V x) : E)) μ := hP.add hP
  simp only [Submodule.reflection_apply, Submodule.starProjection_apply, two_smul] at h
  rw [integral_sub hPP.integrableOn hV.integrableOn,
    integral_add hP.integrableOn hP.integrableOn] at h
  have heq : (2 : ℝ) • (∫ x in s, (K.orthogonalProjection (V x) : E) ∂μ) =
      (2 : ℝ) • (∫ x in s, V x ∂μ) := by
    simpa only [two_smul] using sub_eq_iff_eq_add.mp h
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) heq

/-- A symmetry preserving the observation forces the actual conditional mean into its fixed
subspace. This applies to continuous observations and does not assume positive-mass fibers. -/
theorem reflection_observation_condExp_projection (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) (F : α → β) (hF : Measurable F)
    (hfix : ∀ x, F (e x) = F x) (V : α → E) (hV : Integrable V μ)
    (K : Submodule ℝ E) (htransform : ∀ x, V (e x) = K.reflection (V x)) :
    ∀ᵐ x ∂μ, (K.orthogonalProjection ((μ[V | MeasurableSpace.comap F inferInstance]) x) : E) =
      (μ[V | MeasurableSpace.comap F inferInstance]) x := by
  let m := MeasurableSpace.comap F inferInstance
  letI : MeasurableSpace α := mα
  let M := μ[V | m]
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  have hM : Integrable M μ := integrable_condExp
  have hP : Integrable (fun x => P (M x)) μ := P.integrable_comp hM
  apply ae_eq_condExp_of_forall_setIntegral_eq hF.comap_le hV
    (fun _ _ _ => hP.integrableOn)
  · intro s hs hfinite
    calc
      (∫ x in s, P (M x) ∂μ) = P (∫ x in s, M x ∂μ) := P.integral_comp_comm hM.restrict
      _ = P (∫ x in s, V x ∂μ) := by rw [setIntegral_condExp hF.comap_le hV hs]
      _ = ∫ x in s, P (V x) ∂μ := (P.integral_comp_comm hV.restrict).symm
      _ = ∫ x in s, V x ∂μ :=
        reflection_observation_setIntegral μ e he F hF hfix V hV K htransform hs
  · exact P.continuous.comp_aestronglyMeasurable
      (stronglyMeasurable_condExp.aestronglyMeasurable)

theorem reflection_observation_condExp_energy (μ : Measure α) [IsProbabilityMeasure μ]
    (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) (F : α → β) (hF : Measurable F)
    (hfix : ∀ x, F (e x) = F x) (V : α → E) (hV : MemLp V 2 μ)
    {u : E} (hu : ‖u‖ = 1) (htransform : ∀ x, V (e x) = (ℝ ∙ u).reflection (V x)) :
    (∫ x, ‖(μ[V | MeasurableSpace.comap F inferInstance]) x‖ ^ 2 ∂μ) ≤
      ∫ x, ⟪u, V x⟫_ℝ ^ 2 ∂μ := by
  have hp := reflection_observation_condExp_projection μ e he F hF hfix V
    (hV.integrable (by norm_num)) (ℝ ∙ u) htransform
  have hnorm : (∫ x, ‖(μ[V | MeasurableSpace.comap F inferInstance]) x‖ ^ 2 ∂μ) =
      ∫ x, ⟪u, (μ[V | MeasurableSpace.comap F inferInstance]) x⟫_ℝ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [unit_orthogonalProjection_formula hu] at hx
    conv_lhs => rw [← hx, norm_smul, hu]
    simp [real_inner_comm u]
  rw [hnorm]
  have hres := conditional_direction_residual_energy hF.comap_le hV u
  linarith [integral_nonneg (μ := μ)
    (f := fun x : α => ⟪u, V x - (μ[V | MeasurableSpace.comap F inferInstance]) x⟫_ℝ ^ 2)
    (fun x => sq_nonneg ⟪u, V x - (μ[V | MeasurableSpace.comap F inferInstance]) x⟫_ℝ)]

end
end Nonsmooth
