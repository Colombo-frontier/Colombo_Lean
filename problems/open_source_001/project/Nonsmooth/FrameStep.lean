import Nonsmooth.SphericalFrame

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def initialSphericalFrame : SphericalFrame (⊥ : Submodule ℝ E) where
  equiv := MeasurableEquiv.refl E
  preserving := MeasurePreserving.id _
  rotation := fun _ => LinearIsometryEquiv.refl ℝ E
  known := fun _ => measurable_const
  inverse_apply := fun _ => rfl

theorem initialSphericalFrame_information :
    frameInformation (initialSphericalFrame (E := E)) = ⊥ := by
  simp only [frameInformation, initialSphericalFrame, projectionInformation_bot,
    MeasurableSpace.comap_bot]

variable {K L : Submodule ℝ E} (F : SphericalFrame K)

theorem frame_equiv_symm_observation_measurable :
    @Measurable E E (projectionInformation K) (frameInformation F) F.equiv.symm := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap F.equiv.symm (MeasurableSpace.comap F.equiv (projectionInformation K)) ≤ _
  rw [MeasurableSpace.comap_comp]
  have he : (F.equiv ∘ F.equiv.symm : E → E) = id := by
    funext y
    exact F.equiv.apply_symm_apply y
  rw [he, MeasurableSpace.comap_id]

def rotateSphericalFrame (hr : 0 < Module.finrank ℝ Kᗮ) (w : E → E)
    (hw : @Measurable E E (projectionInformation K) mE w) (hwp : ∀ y, w y ∈ Kᗮ)
    (hKL : K ≤ L) : SphericalFrame L := by
  let H := historyReflectionEquiv K hr w hw hwp
  refine {
    equiv := F.equiv.trans H
    preserving := (historyReflectionEquiv_preserving K hr w hw hwp).comp F.preserving
    rotation := fun y => (ℝ ∙ w y)ᗮ.reflection.trans (F.rotation y)
    known := ?_
    inverse_apply := ?_
  }
  · intro v
    have hv : @Measurable E E (projectionInformation K) mE
        (fun y => perpendicularReflection (w y) v) := (perpendicularReflection_measurable v).comp hw
    have hm := @measurable_variable_isometry E _ _ mE _ _ _ E (projectionInformation K)
      F.rotation F.known _ hv
    exact hm.mono (projectionInformation_mono hKL) le_rfl
  · intro y
    change F.equiv.symm (perpendicularReflection (w y) y) =
      F.rotation y (perpendicularReflection (w y) y)
    have hp : K.orthogonalProjection (perpendicularReflection (w y) y) = K.orthogonalProjection y :=
      projection_reflection_perpendicular K (hwp y) y
    rw [F.inverse_apply, frame_rotation_fiber F hp]

theorem rotateSphericalFrame_information (hr : 0 < Module.finrank ℝ Kᗮ) (w : E → E)
    (hw : @Measurable E E (projectionInformation K) mE w) (hwp : ∀ y, w y ∈ Kᗮ)
    (hKL : K ≤ L) :
    frameInformation (rotateSphericalFrame F hr w hw hwp hKL) = MeasurableSpace.comap F.equiv
      (MeasurableSpace.comap (fun y => perpendicularReflection (w y) y) (projectionInformation (mE := mE) L)) := by
  rw [MeasurableSpace.comap_comp]
  rfl

theorem alignedSphericalFrame_information (hr : 0 < Module.finrank ℝ Kᗮ) (U : E → E)
    (hU : @Measurable E E (projectionInformation K) mE U)
    (hUp : ∀ y, U y ∈ Kᗮ) (hUn : ∀ y, ‖U y‖ = 1) (e : E)
    (he : e ∈ Kᗮ) (hen : ‖e‖ = 1) :
    frameInformation (rotateSphericalFrame F hr (fun y => U y - e) (hU.sub measurable_const)
      (fun y => Kᗮ.sub_mem (hUp y) he) (le_sup_left : K ≤ K ⊔ ℝ ∙ e)) =
        MeasurableSpace.comap F.equiv (oneMoreLinearInformation (mE := mE) K U) := by
  rw [rotateSphericalFrame_information, alignment_information K U hUp hUn e he hen]

/-- Any one measurable query admits an orthogonal frame extension of rank one. Zero and
redundant queries are included by measurable orthogonal completion. -/
theorem spherical_frame_one_query (hr : 0 < Module.finrank ℝ Kᗮ) (q : E → E)
    (hq : @Measurable E E (frameInformation F) mE q) :
    ∃ (L : Submodule ℝ E) (G : SphericalFrame L),
      Module.finrank ℝ L = Module.finrank ℝ K + 1 ∧
      frameInformation F ⊔ MeasurableSpace.comap (fun x => ⟪q x, x⟫_ℝ) inferInstance ≤
        frameInformation G := by
  let Q : E → E := fun y => (F.rotation y).symm (q (F.equiv.symm y))
  have hq' : @Measurable E E (projectionInformation K) mE (fun y => q (F.equiv.symm y)) :=
    hq.comp (frame_equiv_symm_observation_measurable F)
  have hQ : @Measurable E E (projectionInformation K) mE Q :=
    @measurable_variable_isometry_symm E _ _ mE _ _ _ E (projectionInformation K)
      F.rotation F.known _ hq'
  let U : E → E := fun y => completionDirection K (Q y)
  have hU : @Measurable E E (projectionInformation K) mE U :=
    (completionDirection_measurable K).comp hQ
  have hUp : ∀ y, U y ∈ Kᗮ := fun y => completionDirection_mem K (Q y)
  have hUn : ∀ y, ‖U y‖ = 1 := fun y => completionDirection_norm K hr (Q y)
  let e := fallbackOrthogonal K
  have he : e ∈ Kᗮ := fallbackOrthogonal_mem K
  have hen : ‖e‖ = 1 := fallbackOrthogonal_norm K hr
  let L := K ⊔ ℝ ∙ e
  let G : SphericalFrame L := rotateSphericalFrame F hr (fun y => U y - e)
    (hU.sub measurable_const) (fun y => Kᗮ.sub_mem (hUp y) he) le_sup_left
  refine ⟨L, G, orthogonal_unit_extension_finrank K he hen, ?_⟩
  have hinfo : frameInformation G = MeasurableSpace.comap F.equiv (oneMoreLinearInformation (mE := mE) K U) :=
    alignedSphericalFrame_information F hr U hU hUp hUn e he hen
  rw [hinfo]
  apply sup_le (MeasurableSpace.comap_mono (show projectionInformation K ≤ oneMoreLinearInformation K U from le_sup_left))
  have hresponse : @Measurable E ℝ (oneMoreLinearInformation K U) inferInstance
      (fun y => ⟪Q y, y⟫_ℝ) := variable_query_response_measurable K U Q hU hQ hUp hUn
        (fun y => completionDirection_contains K (Q y))
  have hcomp : @Measurable E ℝ (MeasurableSpace.comap F.equiv (oneMoreLinearInformation (mE := mE) K U))
      inferInstance (fun x => ⟪Q (F.equiv x), F.equiv x⟫_ℝ) :=
    hresponse.comp (measurable_iff_comap_le.mpr le_rfl)
  have heq (x : E) : ⟪Q (F.equiv x), F.equiv x⟫_ℝ = ⟪q x, x⟫_ℝ := by
    simp only [Q, F.equiv.symm_apply_apply]
    have h := (F.rotation (F.equiv x)).inner_map_map
      ((F.rotation (F.equiv x)).symm (q x)) (F.equiv x)
    simpa only [LinearIsometryEquiv.apply_symm_apply, frame_inverse_at_equiv F] using h.symm
  simp only [heq] at hcomp
  exact measurable_iff_comap_le.mp hcomp

end
end Nonsmooth
