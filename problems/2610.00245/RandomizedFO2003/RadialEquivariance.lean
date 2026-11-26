import RandomizedFO2003.RadialGate
import RandomizedFO2003.RotationGroup

namespace RandomizedFO2003.Primitives

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unitRadialSquash_isometry (U : E ≃ₗᵢ[ℝ] E) (x : E) :
    unitRadialSquash (U x) = U (unitRadialSquash x) := by
  simp only [unitRadialSquash, U.inner_map_map, map_smul]

theorem radialSquash_isometry (U : E ≃ₗᵢ[ℝ] E) (B : ℝ) (x : E) :
    radialSquash B (U x) = U (radialSquash B x) := by
  simp only [radialSquash, ← map_smul, unitRadialSquash_isometry]

theorem radialReadout_isometry (U : E ≃ₗᵢ[ℝ] E) (a : E) (B α : ℝ) (x : E) :
    radialReadout (U a) B α x = radialReadout a B α (U.symm x) := by
  unfold radialReadout
  rw [← U.apply_symm_apply x, radialSquash_isometry, U.inner_map_map, U.symm_apply_apply]

variable [FiniteDimensional ℝ E]

theorem radialReadout_rotation (U : Rotations.Rotation E) (a : E) (B α : ℝ) (x : E) :
    radialReadout (Rotations.isometry E U a) B α x =
      radialReadout a B α ((U : E →L[ℝ] E).adjoint x) := by
  rw [radialReadout_isometry]
  rfl

end RandomizedFO2003.Primitives
