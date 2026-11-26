import RandomizedFO2003.SphereLaw
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace RandomizedFO2003.Rotations

open MeasureTheory Set TopologicalSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Orthogonal transformations represented as unitary continuous linear maps.
The subtype carries the operator-norm topology. -/
abbrev Rotation := unitary (E →L[ℝ] E)

instance rotationTopologicalGroup : IsTopologicalGroup (Rotation E) where
  continuous_mul := continuous_mul
  continuous_inv := continuous_subtype_val.star.subtype_mk _

theorem rotation_isClosed : IsClosed (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)) :=
  (isClosed_eq (continuous_id.star.mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.mul continuous_id.star) continuous_const)

theorem rotation_norm_le (U : Rotation E) : ‖(U : E →L[ℝ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [unitary.norm_map]

instance rotationCompactSpace : CompactSpace (Rotation E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset (rotation_isClosed E)
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right] using rotation_norm_le E ⟨U, hU⟩

instance rotationMeasurableSpace : MeasurableSpace (Rotation E) := Subtype.instMeasurableSpace

instance rotationBorelSpace : BorelSpace (Rotation E) := Subtype.borelSpace _

noncomputable def isometry (U : Rotation E) : E ≃ₗᵢ[ℝ] E := unitary.linearIsometryEquiv U

@[simp] theorem isometry_apply (U : Rotation E) (x : E) :
    isometry E U x = (U : E →L[ℝ] E) x := rfl

@[simp] theorem isometry_mul (U V : Rotation E) (x : E) :
    isometry E (U * V) x = isometry E U (isometry E V x) := rfl

@[simp] theorem isometry_one (x : E) : isometry E 1 x = x := rfl

@[simp] theorem isometry_inv (U : Rotation E) :
    isometry E U⁻¹ = (isometry E U).symm :=
  unitary.linearIsometryEquiv.map_inv U

theorem continuous_action : Continuous (fun p : Rotation E × E => isometry E p.1 p.2) :=
  (continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd

/-- Haar probability is normalized on the whole compact orthogonal group. -/
noncomputable def haarLaw : Measure (Rotation E) := Measure.haarMeasure ⊤

instance haarLaw_probability : IsProbabilityMeasure (haarLaw E) := by
  constructor
  exact Measure.haarMeasure_self

instance haarLaw_isHaar : (haarLaw E).IsHaarMeasure := by
  unfold haarLaw
  infer_instance

theorem haar_left (Q : Rotation E) :
    MeasurePreserving (fun U => Q * U) (haarLaw E) (haarLaw E) :=
  measurePreserving_mul_left (haarLaw E) Q

instance haarLaw_rightInvariant : (haarLaw E).IsMulRightInvariant where
  map_mul_right_eq_self Q := by
    haveI : IsProbabilityMeasure ((haarLaw E).map (fun U => U * Q)) :=
      isProbabilityMeasure_map (measurable_mul_const Q).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem haar_right (Q : Rotation E) :
    MeasurePreserving (fun U => U * Q) (haarLaw E) (haarLaw E) :=
  measurePreserving_mul_right (haarLaw E) Q

instance haarLaw_invInvariant : (haarLaw E).IsInvInvariant where
  inv_eq_self := by
    haveI : IsProbabilityMeasure ((haarLaw E).inv) :=
      isProbabilityMeasure_map measurable_inv.aemeasurable
    haveI : ((haarLaw E).inv).IsHaarMeasure :=
      Measure.isHaarMeasure_of_isCompact_nonempty_interior (haarLaw E).inv Set.univ
        isCompact_univ (by simp) (by simp) (by simp)
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem haar_inverse : MeasurePreserving (Inv.inv : Rotation E → Rotation E) (haarLaw E) (haarLaw E) :=
  Measure.measurePreserving_inv (haarLaw E)

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_action : Measurable (fun p : Rotation E × E => isometry E p.1 p.2) :=
  (continuous_action E).measurable

/-- The latent sphere vector and the rotated physical vector have the same
product law with the Haar rotation. -/
theorem haar_sphere_product :
    MeasurePreserving (fun p : Rotation E × E => (p.1, isometry E p.1 p.2))
      ((haarLaw E).prod (Spherical.sphereLaw E)) ((haarLaw E).prod (Spherical.sphereLaw E)) :=
  Spherical.random_rotation_product E (haarLaw E) (isometry E) (measurable_action E)

end RandomizedFO2003.Rotations
