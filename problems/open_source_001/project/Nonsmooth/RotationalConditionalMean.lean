import Nonsmooth.GaussianRowCovarianceResidual
import Nonsmooth.FixedProjection

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem reflection_projection_setIntegral (μ : Measure E) (hi : Integrable (fun x : E => x) μ)
    (K : Submodule ℝ E) (hinv : μ.map K.reflection = μ) {s : Set E}
    (hs : MeasurableSet[projectionInformation K] s) :
    (∫ x in s, (K.orthogonalProjection x : E) ∂μ) = ∫ x in s, x ∂μ := by
  have hsm : MeasurableSet s := projectionInformation_le K s hs
  have hpre := projection_event_reflection K hs
  have hfun : (fun x => s.indicator (fun y : E => y) (K.reflection x)) =
      s.indicator (fun x => K.reflection x) := by
    funext x
    have hmem : K.reflection x ∈ s ↔ x ∈ s := by
      change x ∈ K.reflection ⁻¹' s ↔ x ∈ s
      rw [hpre]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]
  have hp : MeasurePreserving K.reflection μ μ := ⟨K.reflection.continuous.measurable, hinv⟩
  have h := hp.integral_comp K.reflection.toMeasurableEquiv.measurableEmbedding (s.indicator (fun y : E => y))
  rw [hfun, integral_indicator hsm, integral_indicator hsm] at h
  have hiP : Integrable (fun x => (K.orthogonalProjection x : E)) μ :=
    (K.subtypeL.comp K.orthogonalProjection).integrable_comp hi
  simp only [Submodule.reflection_apply, Submodule.starProjection_apply, two_smul] at h
  have hPP : Integrable (fun x => (K.orthogonalProjection x : E) +
      (K.orthogonalProjection x : E)) μ := hiP.add hiP
  rw [integral_sub hPP.integrableOn hi.integrableOn,
    integral_add hiP.integrableOn hiP.integrableOn] at h
  have he : (2 : ℝ) • (∫ x in s, (K.orthogonalProjection x : E) ∂μ) =
      (2 : ℝ) • (∫ x in s, x ∂μ) := by
    simpa only [two_smul] using sub_eq_iff_eq_add.mp h
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) he

theorem reflection_condExp_projection (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : E => x) μ) (K : Submodule ℝ E) (hinv : μ.map K.reflection = μ) :
    (fun x : E => (K.orthogonalProjection x : E)) =ᵐ[μ] μ[fun x : E => x | projectionInformation K] := by
  have hiP : Integrable (fun x => (K.orthogonalProjection x : E)) μ :=
    (K.subtypeL.comp K.orthogonalProjection).integrable_comp hi
  apply ae_eq_condExp_of_forall_setIntegral_eq (projectionInformation_le K) hi
    (fun _ _ _ => hiP.integrableOn) (fun _ hs _ => reflection_projection_setIntegral μ hi K hinv hs)
  have hm : @Measurable E E (projectionInformation K) mE
      (fun x => (K.orthogonalProjection x : E)) := measurable_iff_comap_le.mpr le_rfl
  exact hm.aestronglyMeasurable

theorem unit_orthogonalProjection_formula {u : E} (hu : ‖u‖ = 1) (z : E) :
    (((ℝ ∙ u).orthogonalProjection z) : E) = ⟪z, u⟫_ℝ • u := by
  change (ℝ ∙ u).starProjection z = _
  rw [Submodule.starProjection_singleton]
  simp [hu, real_inner_comm u]

theorem unit_inner_projection_information {u : E} (hu : ‖u‖ = 1) :
    MeasurableSpace.comap (fun z : E => ⟪z, u⟫_ℝ)
      (inferInstance : MeasurableSpace ℝ) = projectionInformation (ℝ ∙ u) := by
  apply le_antisymm
  · apply measurable_iff_comap_le.mp
    have hp : @Measurable E E (projectionInformation (ℝ ∙ u)) mE
        (fun z => (((ℝ ∙ u).orthogonalProjection z) : E)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hf : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
      (continuous_id.inner continuous_const).measurable
    have hh := hf.comp hp
    convert hh using 1
    funext z
    dsimp only [Function.comp_def]
    rw [unit_orthogonalProjection_formula hu, inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    simp
  · apply measurable_iff_comap_le.mp
    have hr : @Measurable E ℝ
        (MeasurableSpace.comap (fun z : E => ⟪z, u⟫_ℝ) inferInstance)
        inferInstance (fun z => ⟪z, u⟫_ℝ) := measurable_iff_comap_le.mpr le_rfl
    convert hr.smul_const u using 1
    funext z
    exact unit_orthogonalProjection_formula hu z

/-- Reflection invariance identifies the barycenter of almost every regular projection slice.
No conditioning on a positive-mass singleton is used. -/
theorem reflection_projection_slice_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : E => x) μ) {u : E} (hu : ‖u‖ = 1)
    (hinv : μ.map (ℝ ∙ u).reflection = μ) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      (∫ z, z ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ y) = y • u := by
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hp := reflection_condExp_projection μ hi (ℝ ∙ u) hinv
  rw [← unit_inner_projection_information hu] at hp
  have hc := condExp_ae_eq_integral_condDistrib_id hr hi
  have hm : StronglyMeasurable (fun y : ℝ =>
      ∫ z, z ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ y) :=
    (continuous_snd.stronglyMeasurable :
      StronglyMeasurable (fun p : ℝ × E => p.2)).integral_condDistrib
  apply (ae_map_iff hr.aemeasurable
    (measurableSet_eq_fun hm.measurable (measurable_id.smul_const u))).mpr
  filter_upwards [hp, hc] with z hz hzc
  rw [← hzc, ← hz, unit_orthogonalProjection_formula hu]
  rfl

theorem gaussianAmbientRowLaw_projection_slice_mean [Nontrivial E]
    {u : E} (hu : ‖u‖ = 1) :
    ∀ᵐ y ∂(gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ),
      (∫ z, z ∂condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (gaussianAmbientRowLaw E) y) =
        y • u :=
  reflection_projection_slice_mean _
    (gaussianAmbientRowLaw_memLp.integrable (by norm_num)) hu
    (gaussianAmbientRowLaw_isometry (ℝ ∙ u).reflection)

theorem reflection_event_mean_projection (μ : Measure E)
    (hi : Integrable (fun x : E => x) μ) (K : Submodule ℝ E)
    (hinv : μ.map K.reflection = μ) {s : Set E}
    (hs : MeasurableSet[projectionInformation K] s) :
    (K.orthogonalProjection (∫ x, x ∂μ[|s]) : E) = ∫ x, x ∂μ[|s] := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  have hc : (∫ x in s, (K.orthogonalProjection x : E) ∂μ) =
      (K.orthogonalProjection (∫ x in s, x ∂μ) : E) := P.integral_comp_comm hi.restrict
  have he := hc.symm.trans (reflection_projection_setIntegral μ hi K hinv hs)
  simp only [ProbabilityTheory.cond, integral_smul_measure, map_smul,
    Submodule.coe_smul, he]

theorem reflection_projection_event_mean (μ : Measure E)
    (hi : Integrable (fun x : E => x) μ) {u : E} (hu : ‖u‖ = 1)
    (hinv : μ.map (ℝ ∙ u).reflection = μ) {D : Set ℝ} (hD : MeasurableSet D) :
    (∫ z, z ∂μ[|(fun z : E => ⟪z, u⟫_ℝ) ⁻¹' D]) =
      ⟪(∫ z, z ∂μ[|(fun z : E => ⟪z, u⟫_ℝ) ⁻¹' D]), u⟫_ℝ • u := by
  have hs : MeasurableSet[projectionInformation (ℝ ∙ u)]
      ((fun z : E => ⟪z, u⟫_ℝ) ⁻¹' D) := by
    rw [← unit_inner_projection_information hu]
    exact (Measurable.of_comap_le le_rfl) hD
  have he := reflection_event_mean_projection μ hi (ℝ ∙ u) hinv hs
  rw [unit_orthogonalProjection_formula hu] at he
  exact he.symm

end
end Nonsmooth
