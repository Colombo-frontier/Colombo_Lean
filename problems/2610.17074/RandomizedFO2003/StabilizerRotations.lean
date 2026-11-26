import RandomizedFO2003.ComplementRotations

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def fixingSubgroup (L : Submodule ℝ E) : Subgroup (Rotation E) where
  carrier := {U | ∀ x : L, isometry E U x = x}
  one_mem' := by intro x; rfl
  mul_mem' hU hV := by intro x; rw [isometry_mul, hV, hU]
  inv_mem' hU := by
    intro x
    rw [isometry_inv]
    apply (isometry E _).injective
    rw [LinearIsometryEquiv.apply_symm_apply, hU]

theorem fixed_complement_mem (L : Submodule ℝ E) (U : fixingSubgroup L) (x : Lᗮ) :
    isometry E U.val x ∈ Lᗮ := by
  apply (L.mem_orthogonal _).mpr
  intro y hy
  have hfix : isometry E U.val y = y := U.property ⟨y, hy⟩
  rw [← hfix, (isometry E U.val).inner_map_map]
  exact (L.mem_orthogonal _).mp x.property y hy

noncomputable def restrictComplementIsometry (L : Submodule ℝ E) (U : fixingSubgroup L) :
    Lᗮ ≃ₗᵢ[ℝ] Lᗮ where
  toFun x := ⟨isometry E U.val x, fixed_complement_mem L U x⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _
  invFun x := ⟨isometry E U⁻¹.val x, fixed_complement_mem L U⁻¹ x⟩
  left_inv x := by
    apply Subtype.ext
    change isometry E U.val⁻¹ (isometry E U.val x) = x
    rw [isometry_inv, LinearIsometryEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change isometry E U.val (isometry E U.val⁻¹ x) = x
    rw [isometry_inv, LinearIsometryEquiv.apply_symm_apply]
  norm_map' x := (isometry E U.val).norm_map x

noncomputable def restrictComplement (L : Submodule ℝ E) (U : fixingSubgroup L) : Rotation Lᗮ :=
  unitary.linearIsometryEquiv.symm (restrictComplementIsometry L U)

@[simp] theorem restrictComplement_apply (L : Submodule ℝ E) (U : fixingSubgroup L) (x : Lᗮ) :
    (isometry Lᗮ (restrictComplement L U) x : E) = isometry E U.val x := rfl

noncomputable def extendToFixing (L : Submodule ℝ E) (R : Rotation Lᗮ) : fixingSubgroup L :=
  ⟨extendComplement L R, extendComplement_fixed L R⟩

@[simp] theorem restrict_extend (L : Submodule ℝ E) (R : Rotation Lᗮ) :
    restrictComplement L (extendToFixing L R) = R := by
  apply Subtype.ext
  ext x
  change isometry E (extendComplement L R) (x : E) = (isometry Lᗮ R x : E)
  exact extendComplement_on_orthogonal L R x

@[simp] theorem extend_restrict (L : Submodule ℝ E) (U : fixingSubgroup L) :
    extendToFixing L (restrictComplement L U) = U := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  change isometry E (extendComplement L (restrictComplement L U)) x = isometry E U.val x
  rw [extendComplement_apply, restrictComplement_apply]
  conv_rhs => rw [← L.orthogonalProjection_add_orthogonalProjection_orthogonal x,
    map_add, U.property (L.orthogonalProjection x)]

/-- The full pointwise stabilizer is exactly the orthogonal group of the
unexposed complement, including zero-dimensional complements. -/
noncomputable def complementStabilizerEquiv (L : Submodule ℝ E) :
    Rotation Lᗮ ≃* fixingSubgroup L where
  toFun := extendToFixing L
  invFun := restrictComplement L
  left_inv := restrict_extend L
  right_inv := extend_restrict L
  map_mul' U V := Subtype.ext (extendComplement_mul L U V)

theorem continuous_extendToFixing (L : Submodule ℝ E) : Continuous (extendToFixing L) :=
  (continuous_extendComplement L).subtype_mk _

theorem continuous_restrictComplement (L : Submodule ℝ E) : Continuous (restrictComplement L) := by
  have hc : Continuous (fun U : fixingSubgroup L =>
      Lᗮ.orthogonalProjection.comp (((U.val : E →L[ℝ] E)).comp Lᗮ.subtypeL)) := by fun_prop
  apply (continuous_induced_rng).mpr
  convert hc using 1
  funext U
  ext x
  change (isometry Lᗮ (restrictComplement L U) x : E) =
    (Lᗮ.orthogonalProjection (isometry E U.val (x : E)) : E)
  symm
  exact congrArg (fun y : Lᗮ => (y : E)) (Submodule.orthogonalProjection_mem_subspace_eq_self
    ⟨isometry E U.val x, fixed_complement_mem L U x⟩)

end RandomizedFO2003.Rotations
