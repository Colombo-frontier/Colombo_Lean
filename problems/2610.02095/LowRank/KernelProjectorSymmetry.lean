import LowRank.KernelProjector

/-! Signed row changes and row permutations act on the explicit kernel
projector by the corresponding conjugation, including singular inputs. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem leftKernelProjector_signed_rows (D : Matrix m n ℝ) (a : m → ℝ)
    (ha : ∀ i, a i * a i = 1) (i j : m) :
    leftKernelProjector (fun k l => a k * D k l) i j = a i * leftKernelProjector D i j * a j := by
  have ho : (Matrix.diagonal a)ᵀ * Matrix.diagonal a = 1 := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp only [ha, Matrix.diagonal_one]
  have h := leftKernelProjector_orthogonal_conjugate D (Matrix.diagonal a) ho
  have hm : Matrix.diagonal a * D = fun k l => a k * D k l := by
    ext k l
    simp
  rw [hm] at h
  simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_transpose]
    using congrFun (congrFun h i) j

theorem leftKernelProjector_reindex_rows (D : Matrix m n ℝ) (e : m ≃ m) :
    leftKernelProjector (D.submatrix e id) = (leftKernelProjector D).submatrix e e := by
  have hg : (D.submatrix e id)ᵀ * D.submatrix e id = Dᵀ * D := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  unfold leftKernelProjector
  rw [hg]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    e.injective.eq_iff]

end
end LowRank
