import LowRank.SymmetricFunctionTrace

/-! Two-by-two block matrices reindexed to finite natural dimensions,
with algebraic identities and additivity of spectral sums on diagonal blocks. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def finBlocks {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ) :
    Matrix (Fin (a + b)) (Fin (c + d)) ℝ :=
  (fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem finBlocks_transpose {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ) :
    (finBlocks A B C D)ᵀ = finBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  simp only [finBlocks, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem finBlocks_mul {a b c d e f : ℕ}
    (A : Matrix (Fin a) (Fin c) ℝ) (B : Matrix (Fin a) (Fin d) ℝ)
    (C : Matrix (Fin b) (Fin c) ℝ) (D : Matrix (Fin b) (Fin d) ℝ)
    (E : Matrix (Fin c) (Fin e) ℝ) (F : Matrix (Fin c) (Fin f) ℝ)
    (G : Matrix (Fin d) (Fin e) ℝ) (H : Matrix (Fin d) (Fin f) ℝ) :
    finBlocks A B C D * finBlocks E F G H =
      finBlocks (A * E + B * G) (A * F + B * H) (C * E + D * G) (C * F + D * H) := by
  unfold finBlocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem finBlocks_add {a b c d : ℕ}
    (A E : Matrix (Fin a) (Fin c) ℝ) (B F : Matrix (Fin a) (Fin d) ℝ)
    (C G : Matrix (Fin b) (Fin c) ℝ) (D H : Matrix (Fin b) (Fin d) ℝ) :
    finBlocks A B C D + finBlocks E F G H = finBlocks (A + E) (B + F) (C + G) (D + H) := by
  simp only [finBlocks, ← Matrix.submatrix_add, ← Matrix.fromBlocks_add]
  rfl

theorem finBlocks_one (a b : ℕ) :
    finBlocks (1 : Matrix (Fin a) (Fin a) ℝ) 0 0 (1 : Matrix (Fin b) (Fin b) ℝ) = 1 := by
  simp only [finBlocks, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem finBlocks_zero (a b c d : ℕ) :
    finBlocks (0 : Matrix (Fin a) (Fin c) ℝ) (0 : Matrix (Fin a) (Fin d) ℝ)
      (0 : Matrix (Fin b) (Fin c) ℝ) (0 : Matrix (Fin b) (Fin d) ℝ) = 0 := by
  simp only [finBlocks, Matrix.fromBlocks_zero, Matrix.submatrix_zero]
  rfl

theorem finBlocks_diagonal {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) :
    finBlocks (diagonal x) 0 0 (diagonal y) =
      diagonal (Sum.elim x y ∘ finSumFinEquiv.symm) := by
  simp only [finBlocks, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]

theorem finBlocks_diagonal_isHermitian {a b : ℕ}
    {A : Matrix (Fin a) (Fin a) ℝ} {B : Matrix (Fin b) (Fin b) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (finBlocks A 0 0 B).IsHermitian := by
  have hAT : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hBT : Bᵀ = B := by simpa only [conjTranspose_eq_transpose_of_trivial] using hB.eq
  change (finBlocks A 0 0 B)ᴴ = finBlocks A 0 0 B
  simp only [conjTranspose_eq_transpose_of_trivial, finBlocks_transpose, hAT, hBT, Matrix.transpose_zero]

theorem finBlocks_projector {a b : ℕ}
    {P : Matrix (Fin a) (Fin a) ℝ} {Q : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    IsOrthogonalProjector (finBlocks P 0 0 Q) := by
  constructor
  · simp only [finBlocks_transpose, hP.symmetric, hQ.symmetric, Matrix.transpose_zero]
  · simp only [finBlocks_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hP.idempotent, hQ.idempotent]

theorem finBlocks_projector_complement {a b : ℕ}
    (P : Matrix (Fin a) (Fin a) ℝ) (Q : Matrix (Fin b) (Fin b) ℝ) :
    1 - finBlocks P 0 0 Q = finBlocks (1 - P) 0 0 (1 - Q) := by
  apply sub_eq_iff_eq_add.mpr
  rw [finBlocks_add]
  simp only [sub_add_cancel, add_zero, finBlocks_one]

theorem symmetricFunctionTrace_finBlocks_diagonal {a b : ℕ}
    {A : Matrix (Fin a) (Fin a) ℝ} {B : Matrix (Fin b) (Fin b) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (φ : ℝ → ℝ) :
    symmetricFunctionTrace (finBlocks_diagonal_isHermitian hA hB) φ =
      symmetricFunctionTrace hA φ + symmetricFunctionTrace hB φ := by
  let spA := orderedMatrixSpectrum hA
  let spB := orderedMatrixSpectrum hB
  let U := finBlocks spA.basis 0 0 spB.basis
  have hU : Uᵀ * U = 1 := by
    simp only [U, finBlocks_transpose, Matrix.transpose_zero, finBlocks_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, spA.orthogonal, spB.orthogonal,
      finBlocks_one]
  have hd : Uᵀ * finBlocks A 0 0 B * U =
      diagonal (Sum.elim spA.value spB.value ∘ finSumFinEquiv.symm) := by
    simp only [U, finBlocks_transpose, Matrix.transpose_zero, finBlocks_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, spA.diagonalizes, spB.diagonalizes,
      finBlocks_diagonal]
  rw [symmetricFunctionTrace_eq_of_diagonalization _ _ U hU hd φ]
  change (∑ i, φ (Sum.elim spA.value spB.value (finSumFinEquiv.symm i))) = _
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun i => φ (Sum.elim spA.value spB.value i))]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end
end LowRank
