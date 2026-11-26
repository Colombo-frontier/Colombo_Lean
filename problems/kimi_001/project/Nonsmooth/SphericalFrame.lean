import Nonsmooth.FrameGeometry

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A measurable change of spherical coordinates whose inverse is an orthogonal map determined
by the canonical observations. This structure supplies geometric data, not a posterior axiom. -/
structure SphericalFrame (K : Submodule ℝ E) where
  equiv : E ≃ᵐ E
  preserving : MeasurePreserving equiv (sphericalLaw E) (sphericalLaw E)
  rotation : E → E ≃ₗᵢ[ℝ] E
  known : ∀ v, @Measurable E E (projectionInformation K) mE (fun y => rotation y v)
  inverse_apply : ∀ y, equiv.symm y = rotation y y

variable {K : Submodule ℝ E} (F : SphericalFrame K)

def frameInformation : MeasurableSpace E := MeasurableSpace.comap F.equiv (projectionInformation (mE := mE) K)

def framePosterior (x : E) : E := F.rotation (F.equiv x) (K.orthogonalProjection (F.equiv x))

def frameReflection (x : E) : E := F.equiv.symm (K.reflection (F.equiv x))

theorem frameInformation_le : frameInformation F ≤ mE :=
  (MeasurableSpace.comap_mono (projectionInformation_le K)).trans (measurable_iff_comap_le.mp F.equiv.measurable)

theorem frame_equiv_observation_measurable :
    @Measurable E E (frameInformation F) (projectionInformation K) F.equiv := measurable_iff_comap_le.mpr le_rfl

theorem frame_rotation_fiber {y z : E} (h : K.orthogonalProjection y = K.orthogonalProjection z) :
    F.rotation y = F.rotation z := by
  ext v
  exact projection_known_function_eq K (fun x => F.rotation x v) (F.known v) h

theorem framePosterior_measurable : @Measurable E E (frameInformation F) mE (framePosterior F) := by
  have hA (v : E) : @Measurable E E (frameInformation F) mE (fun x => F.rotation (F.equiv x) v) :=
    (F.known v).comp (frame_equiv_observation_measurable F)
  have hp : @Measurable E E (frameInformation F) mE
      (fun x => (K.orthogonalProjection (F.equiv x) : E)) :=
    (show @Measurable E E (projectionInformation K) mE
      (fun y => (K.orthogonalProjection y : E)) from measurable_iff_comap_le.mpr le_rfl).comp
        (frame_equiv_observation_measurable F)
  exact @measurable_variable_isometry E _ _ mE _ _ _ E (frameInformation F)
    (fun x => F.rotation (F.equiv x)) hA _ hp

theorem frame_inverse_at_equiv (x : E) : F.rotation (F.equiv x) (F.equiv x) = x := by
  rw [← F.inverse_apply, F.equiv.symm_apply_apply]

theorem frameReflection_formula (x : E) : frameReflection F x = (2 : ℝ) • framePosterior F x - x := by
  have hrot : F.rotation (K.reflection (F.equiv x)) = F.rotation (F.equiv x) :=
    frame_rotation_fiber F (orthogonalProjection_reflection K (F.equiv x))
  rw [frameReflection, F.inverse_apply, hrot, Submodule.reflection_apply, Submodule.starProjection_apply, map_sub, map_nsmul]
  simp only [two_smul, frame_inverse_at_equiv F, framePosterior]

theorem frameReflection_involutive : Function.Involutive (frameReflection F) := by
  intro x
  simp only [frameReflection, F.equiv.apply_symm_apply, Submodule.reflection_reflection,
    F.equiv.symm_apply_apply]

theorem frameReflection_event {s : Set E} (hs : MeasurableSet[frameInformation F] s) :
    frameReflection F ⁻¹' s = s := by
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hpre := projection_event_reflection K ht
  ext x
  change F.equiv (frameReflection F x) ∈ t ↔ F.equiv x ∈ t
  simp only [frameReflection, F.equiv.apply_symm_apply]
  change F.equiv x ∈ K.reflection ⁻¹' t ↔ F.equiv x ∈ t
  rw [hpre]

theorem frameReflection_preserving :
    MeasurePreserving (frameReflection F) (sphericalLaw E) (sphericalLaw E) := by
  exact (MeasurePreserving.symm F.equiv F.preserving).comp
    ((sphericalLaw_measurePreserving K.reflection).comp F.preserving)

theorem frame_equiv_norm (x : E) : ‖F.equiv x‖ = ‖x‖ := by
  have h := congrArg norm (frame_inverse_at_equiv F x)
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem framePosterior_norm (x : E) :
    ‖framePosterior F x‖ = ‖(K.orthogonalProjection (F.equiv x) : E)‖ :=
  (F.rotation (F.equiv x)).norm_map _

theorem framePosterior_integrable : Integrable (framePosterior F) (sphericalLaw E) := by
  apply (sphericalLaw_identity_integrable (E := E)).norm.mono'
    ((framePosterior_measurable F).mono (frameInformation_le F) le_rfl).aestronglyMeasurable
  filter_upwards [] with x
  rw [framePosterior_norm]
  have h := (K.orthogonalProjection.le_opNorm (F.equiv x)).trans
    ((mul_le_mul_of_nonneg_right K.orthogonalProjection_norm_le (norm_nonneg (F.equiv x))).trans_eq (one_mul _))
  simpa only [frame_equiv_norm F, ← Submodule.coe_norm] using h

theorem spherical_framePosterior_setIntegral {s : Set E} (hs : MeasurableSet[frameInformation F] s) :
    (∫ x in s, framePosterior F x ∂sphericalLaw E) = ∫ x in s, x ∂sphericalLaw E := by
  have hsm := frameInformation_le F s hs
  have hpre := frameReflection_event F hs
  have hfun : (fun x => s.indicator (fun y : E => y) (frameReflection F x)) =
      s.indicator (frameReflection F) := by
    funext x
    have hmem : frameReflection F x ∈ s ↔ x ∈ s := by
      change x ∈ frameReflection F ⁻¹' s ↔ x ∈ s
      rw [hpre]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.mp h))]
  have hp := frameReflection_preserving F
  let G := MeasurableEquiv.ofInvolutive (frameReflection F) (frameReflection_involutive F) hp.measurable
  have h := hp.integral_comp G.measurableEmbedding (s.indicator (fun y : E => y))
  rw [hfun, integral_indicator hsm, integral_indicator hsm] at h
  have hi := sphericalLaw_identity_integrable (E := E)
  have hM := framePosterior_integrable F
  simp only [frameReflection_formula F, two_smul] at h
  have hMM : Integrable (fun x => framePosterior F x + framePosterior F x) (sphericalLaw E) := hM.add hM
  rw [integral_sub hMM.integrableOn hi.integrableOn,
    integral_add hM.integrableOn hM.integrableOn] at h
  have he : (2 : ℝ) • (∫ x in s, framePosterior F x ∂sphericalLaw E) =
      (2 : ℝ) • (∫ x in s, x ∂sphericalLaw E) := by
    simpa only [two_smul] using sub_eq_iff_eq_add.mp h
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) he

theorem spherical_condExp_frame : framePosterior F =ᵐ[sphericalLaw E]
    (sphericalLaw E)[(fun x : E => x) | frameInformation F] := by
  have hM := framePosterior_integrable F
  apply ae_eq_condExp_of_forall_setIntegral_eq (frameInformation_le F) sphericalLaw_identity_integrable
    (fun _ _ _ => hM.integrableOn) (fun _ hs _ => spherical_framePosterior_setIntegral F hs)
  exact (framePosterior_measurable F).aestronglyMeasurable

theorem spherical_frame_energy :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | frameInformation F]) x‖ ^ 2 ∂sphericalLaw E) =
      (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  calc
    _ = ∫ x, ‖(K.orthogonalProjection (F.equiv x) : E)‖ ^ 2 ∂sphericalLaw E := by
      apply integral_congr_ae
      filter_upwards [spherical_condExp_frame F] with x hx
      rw [← hx, framePosterior_norm]
    _ = ∫ y, ‖(K.orthogonalProjection y : E)‖ ^ 2 ∂sphericalLaw E :=
      F.preserving.integral_comp F.equiv.measurableEmbedding (fun y => ‖(K.orthogonalProjection y : E)‖ ^ 2)
    _ = _ := spherical_projection_second_moment K

theorem spherical_frame_subinformation_energy {m : MeasurableSpace E}
    (hm : m ≤ frameInformation (mE := mE) F) :
    (∫ x, ‖((@sphericalLaw E _ _ mE _ _)[(fun x : E => x) | m]) x‖ ^ 2
      ∂(@sphericalLaw E _ _ mE _ _)) ≤ (Module.finrank ℝ K : ℝ) / (Module.finrank ℝ E : ℝ) := by
  letI : MeasurableSpace E := mE
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have h := condExp_second_moment_mono hm (frameInformation_le F) hV
  rwa [spherical_frame_energy] at h

end
end Nonsmooth
