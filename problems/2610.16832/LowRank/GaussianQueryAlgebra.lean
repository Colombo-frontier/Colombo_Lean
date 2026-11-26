import LowRank.GaussianMatrixColumns
import LowRank.GaussianRevealGram

/-! Pointwise connection between a unit query and its coordinate rotation.
This connects the adaptive distribution step to actual matrix-vector replies. -/

namespace LowRank
open scoped Matrix BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

theorem query_rotation_first_coordinate (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u z : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1) :
    coordinateRotation b (rowGauge b u) z 0 = ∑ i, u i * z i := by
  have h := coordinateRotation_dot b (rowGauge b u) u z
  simp_rw [rowGauge_aligns, hu] at h
  simpa using h

theorem query_rotation_first_row (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (X : Matrix (Fin (r + 1)) (Fin s) ℝ) :
    rotateMatrixColumns b (rowGauge b u) X 0 = Xᵀ *ᵥ u := by
  funext j
  rw [rotateMatrixColumns_apply, query_rotation_first_coordinate b u _ hu]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem rotateMatrixColumns_mulVec (b : OrthonormalBasis (Fin r) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (X : Matrix (Fin r) (Fin s) ℝ) (z : Fin s → ℝ) :
    rotateMatrixColumns b e X *ᵥ z = coordinateRotation b e (X *ᵥ z) := by
  have hsum (Y : Matrix (Fin r) (Fin s) ℝ) :
      Y *ᵥ z = ∑ j, z j • (fun i => Y i j) := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hsum, hsum, map_sum]
  simp_rw [map_smul]
  rfl

theorem query_rotation_gram_reply (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (X : Matrix (Fin (r + 1)) (Fin s) ℝ) :
    let Y := rotateMatrixColumns b (rowGauge b u) X
    (fun i => (Y * Yᵀ) i 0) = coordinateRotation b (rowGauge b u) ((X * Xᵀ) *ᵥ u) := by
  dsimp only
  change rotateMatrixColumns b (rowGauge b u) X *ᵥ
    (rotateMatrixColumns b (rowGauge b u) X 0) = _
  rw [query_rotation_first_row b u hu, rotateMatrixColumns_mulVec, Matrix.mulVec_mulVec]

theorem query_rotation_involutive (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) : Function.Involutive (coordinateRotation b (rowGauge b u)) := by
  intro z
  simp only [coordinateRotation_apply, ContinuousLinearEquiv.symm_apply_apply, rowGauge]
  rw [alignToAxis_involutive]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

end
end LowRank
