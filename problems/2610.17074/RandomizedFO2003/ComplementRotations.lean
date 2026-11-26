import RandomizedFO2003.HaarSphere

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def extendComplementMap (L : Submodule ℝ E) (U : Rotation Lᗮ) : E →L[ℝ] E :=
  L.subtypeL.comp L.orthogonalProjection +
    Lᗮ.subtypeL.comp ((U : Lᗮ →L[ℝ] Lᗮ).comp Lᗮ.orthogonalProjection)

theorem extendComplementMap_apply (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : E) :
    extendComplementMap L U x = (L.orthogonalProjection x : E) +
      (isometry Lᗮ U (Lᗮ.orthogonalProjection x) : E) := rfl

@[simp] theorem project_extendComplementMap (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : E) :
    L.orthogonalProjection (extendComplementMap L U x) = L.orthogonalProjection x := by
  rw [extendComplementMap_apply, map_add]
  simp

@[simp] theorem project_orthogonal_extendComplementMap (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : E) :
    Lᗮ.orthogonalProjection (extendComplementMap L U x) = isometry Lᗮ U (Lᗮ.orthogonalProjection x) := by
  rw [extendComplementMap_apply, map_add]
  simp

theorem extendComplementMap_norm (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : E) :
    ‖extendComplementMap L U x‖ = ‖x‖ := by
  have h := Submodule.norm_sq_eq_add_norm_sq_projection (extendComplementMap L U x) L
  rw [project_extendComplementMap, project_orthogonal_extendComplementMap,
    (isometry Lᗮ U).norm_map, ← Submodule.norm_sq_eq_add_norm_sq_projection] at h
  nlinarith [norm_nonneg (extendComplementMap L U x), norm_nonneg x]

noncomputable def extendComplementIsometry (L : Submodule ℝ E) (U : Rotation Lᗮ) : E ≃ₗᵢ[ℝ] E where
  toLinearMap := (extendComplementMap L U).toLinearMap
  invFun := extendComplementMap L U⁻¹
  left_inv x := by
    change extendComplementMap L U⁻¹ (extendComplementMap L U x) = x
    rw [extendComplementMap_apply, project_extendComplementMap,
      project_orthogonal_extendComplementMap, isometry_inv, LinearIsometryEquiv.symm_apply_apply]
    exact L.orthogonalProjection_add_orthogonalProjection_orthogonal x
  right_inv x := by
    change extendComplementMap L U (extendComplementMap L U⁻¹ x) = x
    rw [extendComplementMap_apply, project_extendComplementMap,
      project_orthogonal_extendComplementMap, isometry_inv, LinearIsometryEquiv.apply_symm_apply]
    exact L.orthogonalProjection_add_orthogonalProjection_orthogonal x
  norm_map' := extendComplementMap_norm L U

/-- Extend a rotation of the unrevealed complement by the identity on the
already exposed subspace. -/
noncomputable def extendComplement (L : Submodule ℝ E) (U : Rotation Lᗮ) : Rotation E :=
  unitary.linearIsometryEquiv.symm (extendComplementIsometry L U)

@[simp] theorem extendComplement_apply (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : E) :
    isometry E (extendComplement L U) x = (L.orthogonalProjection x : E) +
      (isometry Lᗮ U (Lᗮ.orthogonalProjection x) : E) := rfl

@[simp] theorem extendComplement_fixed (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : L) :
    isometry E (extendComplement L U) x = x := by
  have hz : Lᗮ.orthogonalProjection (x : E) = 0 :=
    Submodule.orthogonalProjection_eq_zero_iff.mpr (L.le_orthogonal_orthogonal x.property)
  rw [extendComplement_apply, hz]
  simp

@[simp] theorem extendComplement_on_orthogonal (L : Submodule ℝ E) (U : Rotation Lᗮ) (x : Lᗮ) :
    isometry E (extendComplement L U) x = (isometry Lᗮ U x : E) := by
  rw [extendComplement_apply]; simp

@[simp] theorem extendComplement_one (L : Submodule ℝ E) : extendComplement L 1 = 1 := by
  apply Subtype.ext
  ext x
  exact L.orthogonalProjection_add_orthogonalProjection_orthogonal x

@[simp] theorem extendComplement_mul (L : Submodule ℝ E) (U V : Rotation Lᗮ) :
    extendComplement L (U * V) = extendComplement L U * extendComplement L V := by
  apply Subtype.ext
  ext x
  change extendComplementMap L (U * V) x = extendComplementMap L U (extendComplementMap L V x)
  rw [extendComplementMap_apply, extendComplementMap_apply L U,
    project_extendComplementMap, project_orthogonal_extendComplementMap, isometry_mul]

noncomputable def extendComplementHom (L : Submodule ℝ E) : Rotation Lᗮ →* Rotation E where
  toFun := extendComplement L
  map_one' := extendComplement_one L
  map_mul' := extendComplement_mul L

theorem continuous_extendComplement (L : Submodule ℝ E) : Continuous (extendComplement L) := by
  exact (show Continuous (fun U : Rotation Lᗮ => extendComplementMap L U) from by
    unfold extendComplementMap
    fun_prop).subtype_mk _

@[simp] theorem extendComplement_inv (L : Submodule ℝ E) (U : Rotation Lᗮ) :
    extendComplement L U⁻¹ = (extendComplement L U)⁻¹ :=
  (extendComplementHom L).map_inv U

end RandomizedFO2003.Rotations
