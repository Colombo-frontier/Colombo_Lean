import LowRank.GaussianAdaptiveReply

/-! Orthogonal coordinate maps as concrete matrices. These matrices allow
the local Gaussian gauges to be composed into full row and column bases. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

def gaugeMatrix (b : OrthonormalBasis (Fin r) ℝ E) (e : E ≃ₗᵢ[ℝ] E) :
    Matrix (Fin r) (Fin r) ℝ := LinearMap.toMatrix' (coordinateRotation b e).toLinearMap

theorem gaugeMatrix_apply (b : OrthonormalBasis (Fin r) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (i j : Fin r) : gaugeMatrix b e i j = coordinateRotation b e (Pi.single j 1) i := by
  rw [gaugeMatrix, LinearMap.toMatrix'_apply]
  change coordinateRotation b e (fun k => if k = j then 1 else 0) i = _
  have hv : (fun k : Fin r => if k = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j <;> simp [Pi.single_apply, hk, eq_comm]
  rw [hv]

theorem gaugeMatrix_mulVec (b : OrthonormalBasis (Fin r) ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (z : Fin r → ℝ) : gaugeMatrix b e *ᵥ z = coordinateRotation b e z := by
  change Matrix.toLin' (LinearMap.toMatrix' (coordinateRotation b e).toLinearMap) z = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem gaugeMatrix_transpose_mul_self (b : OrthonormalBasis (Fin r) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) : (gaugeMatrix b e)ᵀ * gaugeMatrix b e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gaugeMatrix_apply]
  have h := coordinateRotation_dot b e (Pi.single i 1) (Pi.single j 1)
  simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using h

theorem gaugeMatrix_mul_transpose_self (b : OrthonormalBasis (Fin r) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) : gaugeMatrix b e * (gaugeMatrix b e)ᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp (gaugeMatrix_transpose_mul_self b e)

theorem rotateMatrixColumns_eq_mul (b : OrthonormalBasis (Fin r) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (X : Matrix (Fin r) (Fin s) ℝ) :
    rotateMatrixColumns b e X = gaugeMatrix b e * X := by
  ext i j
  exact (congrFun (gaugeMatrix_mulVec b e (fun k => X k j)) i).symm

theorem rotateMatrixRows_eq_mul (b : OrthonormalBasis (Fin s) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (X : Matrix (Fin r) (Fin s) ℝ) :
    rotateMatrixRows b e X = X * (gaugeMatrix b e)ᵀ := by
  ext i j
  have h := congrFun (gaugeMatrix_mulVec b e (X i)) j
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    mul_comm] using h.symm

theorem measurable_rowGauge_matrix (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (fun u => gaugeMatrix b (rowGauge b u)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [gaugeMatrix_apply, coordinateRotation_apply, rowGauge, alignToAxis, householder_apply]
  fun_prop

end
end LowRank
