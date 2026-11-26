import VIReference.Pilot.Sphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Support

/-!
# Canonical probability measure on a finite-dimensional unit sphere

This file is kept separate from `Pilot.Sphere` so the conditional tail-bound
module remains a stable compilation checkpoint.
-/

open MeasureTheory ProbabilityTheory Set Real Metric
open scoped Pointwise RealInnerProductSpace

namespace VIReference.Pilot

section CanonicalSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

noncomputable instance canonicalUnitSphereNonempty :
    Nonempty (sphere (0 : E) 1) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨⟨‖x‖⁻¹ • x, ?_⟩⟩
  rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- The finite surface measure induced from the canonical ambient volume. -/
noncomputable def rawSphereFiniteMeasure : FiniteMeasure (sphere (0 : E) 1) :=
  ⟨(volume : Measure E).toSphere, inferInstance⟩

/-- Normalized `volume.toSphere`, hence a canonical spherical probability. -/
noncomputable def canonicalSphereProbability :
    ProbabilityMeasure (sphere (0 : E) 1) :=
  rawSphereFiniteMeasure.normalize

/-- Restriction of an ambient real linear isometry to the unit sphere. -/
noncomputable def unitSphereRotation (U : E ≃ₗᵢ[ℝ] E)
    (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨U x, by
    rw [mem_sphere, dist_zero_right]
    simpa using x.2⟩

@[simp] theorem unitSphereRotation_coe (U : E ≃ₗᵢ[ℝ] E)
    (x : sphere (0 : E) 1) :
    ((unitSphereRotation U x : sphere (0 : E) 1) : E) = U x := rfl

theorem continuous_unitSphereRotation (U : E ≃ₗᵢ[ℝ] E) :
    Continuous (unitSphereRotation U) := by
  apply Continuous.subtype_mk
  exact U.continuous.comp continuous_subtype_val

theorem measurable_unitSphereRotation (U : E ≃ₗᵢ[ℝ] E) :
    Measurable (unitSphereRotation U) :=
  (continuous_unitSphereRotation U).measurable

private theorem unitSphereRotation_cone_preimage (U : E ≃ₗᵢ[ℝ] E)
    (s : Set (sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 •
        ((fun z : sphere (0 : E) 1 => (z : E)) ''
          (unitSphereRotation U ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 •
        ((fun z : sphere (0 : E) 1 => (z : E)) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact ⟨r, hr, unitSphereRotation U z,
      ⟨unitSphereRotation U z, hz, rfl⟩, by simp⟩
  · intro hx
    rcases hx with ⟨r, hr, y, ⟨z, hz, rfl⟩, hry⟩
    refine ⟨r, hr, unitSphereRotation U.symm z, ?_, ?_⟩
    · refine ⟨unitSphereRotation U.symm z, ?_, rfl⟩
      have hrot : unitSphereRotation U (unitSphereRotation U.symm z) = z := by
        apply Subtype.ext
        simp
      change unitSphereRotation U (unitSphereRotation U.symm z) ∈ s
      rwa [hrot]
    · apply U.injective
      simpa using hry

/-- Surface measure induced by ambient volume is invariant under all real
linear isometries. -/
theorem rawSphereMeasure_rotationInvariant (U : E ≃ₗᵢ[ℝ] E) :
    Measure.map (unitSphereRotation U) (volume : Measure E).toSphere =
      (volume : Measure E).toSphere := by
  apply Measure.OuterRegular.ext_isOpen
  intro s hs
  rw [Measure.map_apply (measurable_unitSphereRotation U) hs.measurableSet]
  rw [(volume : Measure E).toSphere_apply'
    ((measurable_unitSphereRotation U) hs.measurableSet)]
  rw [(volume : Measure E).toSphere_apply' hs.measurableSet]
  rw [unitSphereRotation_cone_preimage]
  congr 1
  exact U.measurePreserving.measure_preimage
    (isOpen_Ioo.smul_sphere one_ne_zero (by simp) hs).measurableSet.nullMeasurableSet

private theorem rawSphereFiniteMeasure_ne_zero :
    rawSphereFiniteMeasure (E := E) ≠ 0 := by
  intro h
  apply (volume : Measure E).toSphere_ne_zero
  simpa [rawSphereFiniteMeasure] using
    congrArg (fun m : FiniteMeasure (sphere (0 : E) 1) => m.toMeasure) h

/-- Normalization preserves the rotation invariance of surface measure. -/
theorem canonicalSphereProbability_rotationInvariant (U : E ≃ₗᵢ[ℝ] E) :
    Measure.map (unitSphereRotation U)
        (canonicalSphereProbability (E := E) : Measure (sphere (0 : E) 1)) =
      (canonicalSphereProbability (E := E) : Measure (sphere (0 : E) 1)) := by
  rw [canonicalSphereProbability,
    (rawSphereFiniteMeasure (E := E)).toMeasure_normalize_eq_of_nonzero
      rawSphereFiniteMeasure_ne_zero]
  rw [Measure.map_smul]
  have hraw :
      Measure.map (unitSphereRotation U)
          (rawSphereFiniteMeasure (E := E)).toMeasure =
        (rawSphereFiniteMeasure (E := E)).toMeasure := by
    simpa [rawSphereFiniteMeasure] using rawSphereMeasure_rotationInvariant U
  rw [hraw]

theorem canonicalSphereProbability_isProbability :
    IsProbabilityMeasure
      (canonicalSphereProbability (E := E) : Measure (sphere (0 : E) 1)) :=
  inferInstance

theorem canonicalSphereProbability_unit_ae :
    ∀ᵐ x : sphere (0 : E) 1
      ∂(canonicalSphereProbability (E := E) : Measure (sphere (0 : E) 1)),
      ‖(x : E)‖ = 1 := by
  filter_upwards [] with x
  simpa [mem_sphere, dist_zero_right] using x.2

/-- The canonical construction realizes the abstract uniform-sphere law. -/
theorem canonicalSphereProbability_isUniform :
    IsUniformUnitSphereLaw (Module.finrank ℝ E)
      (fun x : sphere (0 : E) 1 => (x : E))
      (canonicalSphereProbability (E := E) : Measure (sphere (0 : E) 1)) := by
  refine ⟨rfl, continuous_subtype_val.measurable.aemeasurable,
    canonicalSphereProbability_unit_ae, ?_⟩
  intro U
  calc
    Measure.map (fun x : sphere (0 : E) 1 => U (x : E))
        (canonicalSphereProbability (E := E) : Measure _) =
      Measure.map (fun x : sphere (0 : E) 1 => (x : E))
        (Measure.map (unitSphereRotation U)
          (canonicalSphereProbability (E := E) : Measure _)) := by
            rw [Measure.map_map continuous_subtype_val.measurable
              (measurable_unitSphereRotation U)]
            rfl
    _ = Measure.map (fun x : sphere (0 : E) 1 => (x : E))
        (canonicalSphereProbability (E := E) : Measure _) := by
          rw [canonicalSphereProbability_rotationInvariant]

end CanonicalSphere

end VIReference.Pilot
