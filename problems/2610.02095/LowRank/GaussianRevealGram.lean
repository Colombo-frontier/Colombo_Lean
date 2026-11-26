import LowRank.GaussianReveal

/-! The random right gauge preserves the actual Gram matrix. The first column
of the Gram matrix is determined by the exposed row norm and exposed column. -/

namespace LowRank
open MeasureTheory
open scoped BigOperators InnerProductSpace Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

theorem basisCoordinates_dot (b : OrthonormalBasis (Fin s) ℝ E) (x y : E) :
    (∑ j, basisCoordinates b x j * basisCoordinates b y j) = ⟪x, y⟫_ℝ := by
  change (∑ j, b.repr x j * b.repr y j) = _
  simp_rw [b.repr_apply_apply]
  simpa only [real_inner_comm x] using b.sum_inner_mul_inner x y

theorem coordinateRotation_dot (b : OrthonormalBasis (Fin s) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (x y : Fin s → ℝ) :
    (∑ j, coordinateRotation b e x j * coordinateRotation b e y j) = ∑ j, x j * y j := by
  simp_rw [coordinateRotation_apply]
  rw [basisCoordinates_dot, e.inner_map_map, ← basisCoordinates_dot b]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

theorem rotateMatrixRows_gram (b : OrthonormalBasis (Fin s) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (X : Matrix (Fin r) (Fin s) ℝ) :
    (rotateMatrixRows b e X) * (rotateMatrixRows b e X)ᵀ = X * Xᵀ := by
  ext i j
  exact coordinateRotation_dot b e (X i) (X j)

/-- The new oracle column uses only the enlarged exposed state. -/
theorem revealGaussianBlock_gram_column (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) (i : Fin r) :
    (X * Xᵀ) i.succ 0 =
      ‖(basisCoordinates b).symm (X 0)‖ * (revealGaussianBlock b X).1.2 i := by
  rw [← rotateMatrixRows_gram b (rowGauge b (X 0)) X]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rotateMatrixRows]
  simp_rw [rowGauge_aligns]
  simp [revealGaussianBlock, rotateMatrixRows, mul_comm]

theorem revealGaussianBlock_gram_pivot (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    (X * Xᵀ) 0 0 = ‖(basisCoordinates b).symm (X 0)‖ ^ 2 := by
  rw [← rotateMatrixRows_gram b (rowGauge b (X 0)) X]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rotateMatrixRows]
  simp_rw [rowGauge_aligns]
  simp [sq]

end
end LowRank
