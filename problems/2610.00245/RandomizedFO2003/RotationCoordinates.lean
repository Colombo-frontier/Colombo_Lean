import RandomizedFO2003.FrameMeasurability

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {S T E : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def conjugateRotation (V : S ≃ₗᵢ[ℝ] T) (R : Rotation S) : Rotation T :=
  unitary.linearIsometryEquiv.symm ((V.symm.trans (isometry S R)).trans V)

@[simp] theorem conjugateRotation_apply (V : S ≃ₗᵢ[ℝ] T) (R : Rotation S) (x : T) :
    isometry T (conjugateRotation V R) x = V (isometry S R (V.symm x)) := rfl

noncomputable def rotationCoordinates (V : S ≃ₗᵢ[ℝ] T) : Rotation S ≃* Rotation T where
  toFun := conjugateRotation V
  invFun := conjugateRotation V.symm
  left_inv R := by
    apply Subtype.ext
    ext x
    change V.symm (V (isometry S R (V.symm (V x)))) = isometry S R x
    simp
  right_inv R := by
    apply Subtype.ext
    ext x
    change V (V.symm (isometry T R (V (V.symm x)))) = isometry T R x
    simp
  map_mul' R Q := by
    apply Subtype.ext
    ext x
    change V (isometry S R (isometry S Q (V.symm x))) =
      V (isometry S R (V.symm (V (isometry S Q (V.symm x)))))
    simp

theorem continuous_rotationCoordinates (V : S ≃ₗᵢ[ℝ] T) : Continuous (rotationCoordinates V) := by
  exact (show Continuous (fun R : Rotation S =>
      (V : S →L[ℝ] T).comp ((R : S →L[ℝ] S).comp (V.symm : T →L[ℝ] S))) from by
    fun_prop).subtype_mk _

/-- A fixed isometric change of coordinates carries Haar probability to Haar
probability on the new coordinate space. -/
theorem rotationCoordinates_preserving (V : S ≃ₗᵢ[ℝ] T) :
    MeasurePreserving (rotationCoordinates V) (haarLaw S) (haarLaw T) :=
  MonoidHom.measurePreserving (f := (rotationCoordinates V).toMonoidHom)
    (continuous_rotationCoordinates V) (rotationCoordinates V).surjective (by simp)

noncomputable def ExposureFrame.reindex (F : ExposureFrame S E) (V : S ≃ₗᵢ[ℝ] T) : ExposureFrame T E where
  physical := F.physical.comp V.symm.toLinearIsometry
  latent := F.latent.comp V.symm.toLinearIsometry
  known := F.known

theorem ExposureFrame.reindex_operator (F : ExposureFrame S E) (V : S ≃ₗᵢ[ℝ] T) (R : Rotation S) :
    (F.reindex V).operator (rotationCoordinates V R) = F.operator R := by
  unfold ExposureFrame.operator
  congr 1
  change (F.physical.toContinuousLinearMap.comp (V.symm : T →L[ℝ] S)).comp
    ((conjugateRotation V R : T →L[ℝ] T).comp
      (F.latent.toContinuousLinearMap.comp (V.symm : T →L[ℝ] S)).adjoint) = _
  rw [ContinuousLinearMap.adjoint_comp, V.symm.adjoint_eq_symm]
  ext x
  change F.physical (V.symm (V (isometry S R
    (V.symm (V (F.latent.toContinuousLinearMap.adjoint x)))))) = _
  simp

omit [FiniteDimensional ℝ E] in
theorem ExposureFrame.MeasurableFamily.reindex {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → ExposureFrame S E} (hF : ExposureFrame.MeasurableFamily F) (V : S ≃ₗᵢ[ℝ] T) :
    ExposureFrame.MeasurableFamily (fun ω => (F ω).reindex V) := by
  refine ⟨?_, ?_, hF.known⟩
  · change Measurable (fun ω => (F ω).physical.toContinuousLinearMap.comp (V.symm : T →L[ℝ] S))
    exact measurable_operator_comp hF.physical measurable_const
  · change Measurable (fun ω => (F ω).latent.toContinuousLinearMap.comp (V.symm : T →L[ℝ] S))
    exact measurable_operator_comp hF.latent measurable_const

end RandomizedFO2003.Rotations
