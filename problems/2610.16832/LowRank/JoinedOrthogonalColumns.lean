import LowRank.ProjectorBasis

/-! Completing an isometric column matrix to a full orthogonal basis. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def joinColumns {d a b : ℕ} (A : Matrix (Fin d) (Fin a) ℝ)
    (B : Matrix (Fin d) (Fin b) ℝ) : Matrix (Fin d) (Fin a ⊕ Fin b) ℝ :=
  fun i => Sum.elim (A i) (B i)

theorem joinColumns_compression {d a b : ℕ} (A : Matrix (Fin d) (Fin a) ℝ)
    (B : Matrix (Fin d) (Fin b) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (joinColumns A B)ᵀ * M * joinColumns A B =
      fromBlocks (Aᵀ * M * A) (Aᵀ * M * B) (Bᵀ * M * A) (Bᵀ * M * B) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem joinColumns_gram {d a b : ℕ} (A : Matrix (Fin d) (Fin a) ℝ)
    (B : Matrix (Fin d) (Fin b) ℝ) :
    (joinColumns A B)ᵀ * joinColumns A B = fromBlocks (Aᵀ * A) (Aᵀ * B) (Bᵀ * A) (Bᵀ * B) := by
  simpa only [Matrix.mul_one] using joinColumns_compression A B (1 : Matrix (Fin d) (Fin d) ℝ)

theorem column_projector {d m : ℕ} (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) :
    IsOrthogonalProjector (B * Bᵀ) := by
  constructor
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  · calc
      _ = B * (Bᵀ * B) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one]

theorem column_projector_rank {d m : ℕ} (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) :
    (B * Bᵀ).rank = m := by
  have ht : (B * Bᵀ).trace = (m : ℝ) := by
    rw [Matrix.trace_mul_comm, hB, Matrix.trace_one, Fintype.card_fin]
  exact_mod_cast (column_projector B hB).trace_eq_rank.symm.trans ht

theorem exists_orthogonal_complement_columns {k m : ℕ}
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1) :
    ∃ A : Matrix (Fin (k + m)) (Fin k) ℝ,
      Aᵀ * A = 1 ∧ A * Aᵀ = 1 - B * Bᵀ ∧ Aᵀ * B = 0 := by
  have hP := column_projector B hB
  have hrank : (1 - B * Bᵀ).rank = k := by
    have h := projector_rank_complement hP
    rw [column_projector_rank B hB] at h
    omega
  obtain ⟨A, hA, hAA⟩ := projector_basis_factorization hP.complement hrank
  refine ⟨A, hA, hAA, ?_⟩
  calc
    Aᵀ * B = (Aᵀ * A * Aᵀ) * B := by rw [hA, Matrix.one_mul]
    _ = Aᵀ * ((A * Aᵀ) * B) := by simp only [Matrix.mul_assoc]
    _ = Aᵀ * ((1 - B * Bᵀ) * B) := by rw [hAA]
    _ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hB, Matrix.mul_one, sub_self, Matrix.mul_zero]

end
end LowRank
