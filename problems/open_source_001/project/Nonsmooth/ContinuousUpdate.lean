import Nonsmooth.HistoryReflection

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

abbrev UnitPerpendicular (K : Submodule ℝ E) := {u : E // u ∈ Kᗮ ∧ ‖u‖ = 1}

def updatedProjection (K : Submodule ℝ E) (U : E → E) (x : E) : E :=
  (K.orthogonalProjectionOnto x : E) + ⟪U x, x⟫_ℝ • U x

def updatedReflection (K : Submodule ℝ E) (U : E → E) (x : E) : E :=
  (K ⊔ ℝ ∙ U x).reflection x

theorem orthogonalProjection_reflection_of_le {K L : Submodule ℝ E} (hKL : K ≤ L) (x : E) :
    K.orthogonalProjectionOnto (L.reflection x) = K.orthogonalProjectionOnto x := by
  rw [Submodule.reflection_apply, map_sub, map_nsmul,
    Submodule.orthogonalProjectionOnto_starProjection_of_le hKL]
  module

theorem updatedProjection_eq (K : Submodule ℝ E) (U : E → E)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) (x : E) :
    updatedProjection K U x = ((K ⊔ ℝ ∙ U x).orthogonalProjectionOnto x : E) :=
  (orthogonalProjection_unit_extension K (hUp x) (hUn x) x).symm

theorem updatedReflection_formula (K : Submodule ℝ E) (U : E → E)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) (x : E) :
    updatedReflection K U x = (2 : ℝ) • updatedProjection K U x - x := by
  rw [updatedProjection_eq K U hUp hUn]
  simp only [updatedReflection, Submodule.reflection_apply, Submodule.starProjection_apply, two_smul]

theorem unitPerpendicular_reflection_continuous (K : Submodule ℝ E) :
    Continuous (fun p : UnitPerpendicular K × E => (K ⊔ ℝ ∙ p.1.val).reflection p.2) := by
  have hu : Continuous (fun p : UnitPerpendicular K × E => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hp : Continuous (fun p : UnitPerpendicular K × E => (K.orthogonalProjectionOnto p.2 : E)) :=
    (K.subtypeL.comp K.orthogonalProjectionOnto).continuous.comp continuous_snd
  have h : Continuous (fun p : UnitPerpendicular K × E =>
      (2 : ℝ) • ((K.orthogonalProjectionOnto p.2 : E) + ⟪p.1.val, p.2⟫_ℝ • p.1.val) - p.2) :=
    ((hp.add ((hu.inner continuous_snd).smul hu)).const_smul (2 : ℝ)).sub continuous_snd
  convert h using 1
  funext p
  simp only [Submodule.reflection_apply, Submodule.starProjection_apply,
    orthogonalProjection_unit_extension K p.1.property.1 p.1.property.2, two_smul]

/-- Reflection through the enlarged observation space preserves the spherical prior even when
the next direction has an uncountable range and depends measurably on the old projection. -/
theorem spherical_updatedReflection_preserving (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    MeasurePreserving (updatedReflection K U) (sphericalLaw E) (sphericalLaw E) := by
  letI : SecondCountableTopology (UnitPerpendicular K) :=
    TopologicalSpace.Subtype.secondCountableTopology {u : E | u ∈ Kᗮ ∧ ‖u‖ = 1}
  letI : BorelSpace (UnitPerpendicular K) := Subtype.borelSpace {u : E | u ∈ Kᗮ ∧ ‖u‖ = 1}
  let choice : E → UnitPerpendicular K := fun x => ⟨U x, hUp x, hUn x⟩
  have hc : @Measurable E (UnitPerpendicular K) (projectionInformation K) inferInstance choice :=
    hU.subtype_mk
  exact spherical_history_continuous_family (mE := mE) K
    (fun a : UnitPerpendicular K => (K ⊔ ℝ ∙ a.val).reflection)
    (fun a => sphericalLaw_measurePreserving (K ⊔ ℝ ∙ a.val).reflection)
    (unitPerpendicular_reflection_continuous K)
    (fun _ x => orthogonalProjection_reflection_of_le le_sup_left x) choice hc

theorem updatedReflection_involutive (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U) :
    Function.Involutive (updatedReflection K U) := by
  intro x
  have hp : K.orthogonalProjectionOnto (updatedReflection K U x) = K.orthogonalProjectionOnto x :=
    orthogonalProjection_reflection_of_le le_sup_left x
  have he := projection_known_function_eq K U hU hp
  change (K ⊔ ℝ ∙ U (updatedReflection K U x)).reflection ((K ⊔ ℝ ∙ U x).reflection x) = x
  rw [he]
  exact Submodule.reflection_reflection _ x

theorem oneMoreLinearInformation_eq_comap (K : Submodule ℝ E) (U : E → E) :
    oneMoreLinearInformation K U = MeasurableSpace.comap
      (fun x => ((K.orthogonalProjectionOnto x : E), ⟪U x, x⟫_ℝ)) inferInstance := by
  simp only [Prod.instMeasurableSpace, MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp]
  rfl

theorem updatedReflection_response (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U) (x : E) :
    ⟪U (updatedReflection K U x), updatedReflection K U x⟫_ℝ = ⟪U x, x⟫_ℝ := by
  have hp : K.orthogonalProjectionOnto (updatedReflection K U x) = K.orthogonalProjectionOnto x :=
    orthogonalProjection_reflection_of_le le_sup_left x
  rw [projection_known_function_eq K U hU hp]
  let L := K ⊔ ℝ ∙ U x
  have hu : U x ∈ L := (show (ℝ ∙ U x) ≤ L from le_sup_right)
    (Submodule.mem_span_singleton_self (U x))
  have he : L.reflection (U x) = U x := Submodule.reflection_mem_subspace_eq_self hu
  change ⟪U x, L.reflection x⟫_ℝ = _
  have h := L.reflection.inner_map_map (U x) x
  rwa [he] at h

theorem updatedReflection_event (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U) {s : Set E}
    (hs : MeasurableSet[oneMoreLinearInformation K U] s) :
    updatedReflection K U ⁻¹' s = s := by
  rw [oneMoreLinearInformation_eq_comap] at hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  ext x
  change ((K.orthogonalProjectionOnto (updatedReflection K U x) : E),
    ⟪U (updatedReflection K U x), updatedReflection K U x⟫_ℝ) ∈ t ↔
      ((K.orthogonalProjectionOnto x : E), ⟪U x, x⟫_ℝ) ∈ t
  have hp : K.orthogonalProjectionOnto (updatedReflection K U x) = K.orthogonalProjectionOnto x :=
    orthogonalProjection_reflection_of_le le_sup_left x
  rw [hp, updatedReflection_response K U hU]

theorem oneMoreLinearInformation_le (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U) :
    oneMoreLinearInformation K U ≤ mE := by
  apply sup_le (projectionInformation_le K)
  exact measurable_iff_comap_le.mp ((continuous_fst.inner continuous_snd).measurable.comp
    ((hU.mono (projectionInformation_le K) le_rfl).prodMk measurable_id))

theorem updatedProjection_measurable (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U) :
    @Measurable E E (oneMoreLinearInformation K U) mE (updatedProjection K U) := by
  have hp : @Measurable E E (oneMoreLinearInformation K U) mE
      (fun x => (K.orthogonalProjectionOnto x : E)) := measurable_iff_comap_le.mpr le_sup_left
  have hr : @Measurable E ℝ (oneMoreLinearInformation K U) inferInstance
      (fun x => ⟪U x, x⟫_ℝ) := measurable_iff_comap_le.mpr le_sup_right
  exact hp.add (hr.smul (hU.mono le_sup_left le_rfl))

theorem updatedProjection_integrable (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    Integrable (updatedProjection K U) (sphericalLaw E) := by
  apply (sphericalLaw_identity_integrable (E := E)).norm.mono'
    ((updatedProjection_measurable K U hU).mono (oneMoreLinearInformation_le K U hU) le_rfl).aestronglyMeasurable
  filter_upwards [] with x
  rw [updatedProjection_eq K U hUp hUn]
  exact ((K ⊔ ℝ ∙ U x).orthogonalProjectionOnto.le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right (K ⊔ ℝ ∙ U x).orthogonalProjectionOnto_norm_le (norm_nonneg x)).trans_eq (one_mul _))

theorem spherical_updatedProjection_setIntegral (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) {s : Set E}
    (hs : MeasurableSet[oneMoreLinearInformation K U] s) :
    (∫ x in s, updatedProjection K U x ∂sphericalLaw E) = ∫ x in s, x ∂sphericalLaw E := by
  have hsm := oneMoreLinearInformation_le K U hU s hs
  have hpre := updatedReflection_event K U hU hs
  have hfun : (fun x => s.indicator (fun y : E => y) (updatedReflection K U x)) =
      s.indicator (updatedReflection K U) := by
    funext x
    have hmem : updatedReflection K U x ∈ s ↔ x ∈ s := by
      change x ∈ updatedReflection K U ⁻¹' s ↔ x ∈ s
      rw [hpre]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]
  have hp := spherical_updatedReflection_preserving K U hU hUp hUn
  let F := MeasurableEquiv.ofInvolutive (updatedReflection K U)
    (updatedReflection_involutive K U hU) hp.measurable
  have h := hp.integral_comp F.measurableEmbedding (s.indicator (fun y : E => y))
  rw [hfun, integral_indicator hsm, integral_indicator hsm] at h
  have hi := sphericalLaw_identity_integrable (E := E)
  have hM := updatedProjection_integrable K U hU hUp hUn
  simp only [updatedReflection_formula K U hUp hUn, two_smul] at h
  have hMM : Integrable (fun x => updatedProjection K U x + updatedProjection K U x)
      (sphericalLaw E) := hM.add hM
  rw [integral_sub hMM.integrableOn hi.integrableOn,
    integral_add hM.integrableOn hM.integrableOn] at h
  have he : (2 : ℝ) • (∫ x in s, updatedProjection K U x ∂sphericalLaw E) =
      (2 : ℝ) • (∫ x in s, x ∂sphericalLaw E) := by
    simpa only [two_smul] using sub_eq_iff_eq_add.mp h
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) he

/-- Actual posterior after a fixed initial observation and one arbitrary measurable adaptive
unit query. The history contains exactly that one additional scalar response. -/
theorem spherical_condExp_continuous_update (K : Submodule ℝ E) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    updatedProjection K U =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x : E => x) | oneMoreLinearInformation K U] := by
  have hi := sphericalLaw_identity_integrable (E := E)
  have hM := updatedProjection_integrable K U hU hUp hUn
  apply ae_eq_condExp_of_forall_setIntegral_eq (oneMoreLinearInformation_le K U hU) hi
    (fun _ _ _ => hM.integrableOn)
    (fun _ hs _ => spherical_updatedProjection_setIntegral K U hU hUp hUn hs)
  exact (updatedProjection_measurable K U hU).aestronglyMeasurable

/-- No countability premise: the exact posterior energy is (dim K + 1)/d. -/
theorem spherical_continuous_update_energy (K : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ x, U x ∈ Kᗮ) (hUn : ∀ x, ‖U x‖ = 1) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | oneMoreLinearInformation K U]) x‖ ^ 2
      ∂sphericalLaw E) = ((Module.finrank ℝ K : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hp : MemLp (fun x => (K.orthogonalProjectionOnto x : E)) 2 (sphericalLaw E) :=
    (K.subtypeL.comp K.orthogonalProjectionOnto).comp_memLp' hV
  have hpi : Integrable (fun x => ‖(K.orthogonalProjectionOnto x : E)‖ ^ 2) (sphericalLaw E) :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hUi : MemLp (fun x => ⟪U x, x⟫_ℝ) 2 (sphericalLaw E) := by
    apply MemLp.of_bound
      ((continuous_fst.inner continuous_snd).measurable.comp
        ((hU.mono (projectionInformation_le K) le_rfl).prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [sphericalLaw_unit (E := E)] with x hx
    have h := norm_inner_le_norm (𝕜 := ℝ) (U x) x
    simpa only [hUn, hx, one_mul, Function.comp_apply, id_eq] using h
  calc
    _ = ∫ x, ‖(K.orthogonalProjectionOnto x : E)‖ ^ 2 + ⟪U x, x⟫_ℝ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      filter_upwards [spherical_condExp_continuous_update K U hU hUp hUn] with x hx
      rw [← hx, updatedProjection_eq K U hUp hUn]
      exact orthogonalProjection_unit_extension_norm K (hUp x) (hUn x) x
    _ = _ := by
      rw [integral_add hpi hUi.integrable_sq, spherical_projection_second_moment,
        spherical_adapted_unit_direction_second_moment K hr U hU hUp hUn]
      ring

end
end Nonsmooth
