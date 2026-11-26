import RandomizedFO2003.ComplementRotations
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A reference rotation followed by Haar randomness on the unexposed latent
complement. Identifying this law with an adaptive conditional law is a separate
information-theoretic step. -/
noncomputable def compatibleLaw (L : Submodule ℝ E) (U₀ : Rotation E) : Measure (Rotation E) :=
  (haarLaw Lᗮ).map (fun R => U₀ * extendComplement L R)

theorem measurable_compatibleRotation (L : Submodule ℝ E) (U₀ : Rotation E) :
    Measurable (fun R : Rotation Lᗮ => U₀ * extendComplement L R) :=
  (continuous_const.mul (continuous_extendComplement L)).measurable

instance compatibleLaw_probability (L : Submodule ℝ E) (U₀ : Rotation E) :
    IsProbabilityMeasure (compatibleLaw L U₀) :=
  isProbabilityMeasure_map (measurable_compatibleRotation L U₀).aemeasurable

theorem compatibleRotation_fixed (L : Submodule ℝ E) (U₀ : Rotation E) (R : Rotation Lᗮ) (x : L) :
    isometry E (U₀ * extendComplement L R) x = isometry E U₀ x := by
  rw [isometry_mul, extendComplement_fixed]

theorem compatible_inverse_project (L : Submodule ℝ E) (U₀ : Rotation E) (R : Rotation Lᗮ) (x : E) :
    Lᗮ.orthogonalProjection ((isometry E (U₀ * extendComplement L R)).symm x) =
      (isometry Lᗮ R).symm (Lᗮ.orthogonalProjection ((isometry E U₀).symm x)) := by
  rw [← isometry_inv, mul_inv_rev, isometry_mul, ← extendComplement_inv]
  change Lᗮ.orthogonalProjection (extendComplementMap L R⁻¹ (isometry E U₀⁻¹ x)) = _
  rw [project_orthogonal_extendComplementMap, isometry_inv, isometry_inv]

theorem compatible_inverse_exposed (L : Submodule ℝ E) (U₀ : Rotation E) (R : Rotation Lᗮ) (x : E) :
    L.orthogonalProjection ((isometry E (U₀ * extendComplement L R)).symm x) =
      L.orthogonalProjection ((isometry E U₀).symm x) := by
  rw [← isometry_inv, mul_inv_rev, isometry_mul, ← extendComplement_inv]
  change L.orthogonalProjection (extendComplementMap L R⁻¹ (isometry E U₀⁻¹ x)) = _
  rw [project_extendComplementMap, isometry_inv]

variable [MeasurableSpace E] [BorelSpace E]

noncomputable def innovationDirection (L : Submodule ℝ E) (x : E) (U : Rotation E) : Lᗮ :=
  Spherical.radial Lᗮ (Lᗮ.orthogonalProjection ((isometry E U).symm x))

theorem measurable_innovationDirection (L : Submodule ℝ E) (x : E) :
    Measurable (innovationDirection L x) := by
  apply (Spherical.measurable_radial Lᗮ).comp
  apply Lᗮ.orthogonalProjection.continuous.measurable.comp
  simpa only [Function.comp_def, isometry_inv] using (measurable_orbit E x).comp measurable_inv

omit [MeasurableSpace E] [BorelSpace E] in
theorem innovationDirection_compatible (L : Submodule ℝ E) (U₀ : Rotation E)
    (R : Rotation Lᗮ) (x : E) :
    innovationDirection L x (U₀ * extendComplement L R) =
      (isometry Lᗮ R).symm
        (Spherical.radial Lᗮ (Lᗮ.orthogonalProjection ((isometry E U₀).symm x))) := by
  unfold innovationDirection
  rw [compatible_inverse_project, Spherical.radial_commutes]

/-- Under the explicit remaining-rotation law, the next nonzero normalized
latent innovation is exactly uniform on the orthogonal complement. -/
theorem innovationDirection_law (L : Submodule ℝ E) (U₀ : Rotation E) (x : E)
    (hx : Lᗮ.orthogonalProjection ((isometry E U₀).symm x) ≠ 0) :
    (compatibleLaw L U₀).map (innovationDirection L x) = Spherical.sphereLaw Lᗮ := by
  haveI : Nontrivial Lᗮ := ⟨⟨_, _, hx⟩⟩
  unfold compatibleLaw
  rw [Measure.map_map (measurable_innovationDirection L x) (measurable_compatibleRotation L U₀)]
  have heq : innovationDirection L x ∘ (fun R : Rotation Lᗮ => U₀ * extendComplement L R) =
      fun R => (isometry Lᗮ R).symm
        (Spherical.radial Lᗮ (Lᗮ.orthogonalProjection ((isometry E U₀).symm x))) := by
    funext R
    exact innovationDirection_compatible L U₀ R x
  rw [heq]
  exact (haar_inverse_unit_orbit_preserving Lᗮ _ (Spherical.radial_norm Lᗮ hx)).map_eq

end RandomizedFO2003.Rotations
