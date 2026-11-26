import LowRank.BlockKernel

/-! Turning a Loewner bound on the hidden coordinate block into the full
posterior trace inequality. These are deterministic finite-matrix facts. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

variable (a b : Type*) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def topCoordinateProjector : Matrix (a ⊕ b) (a ⊕ b) ℝ :=
  fromBlocks (1 : Matrix a a ℝ) 0 0 (0 : Matrix b b ℝ)

theorem topCoordinateProjector_isProjector : IsOrthogonalProjector (topCoordinateProjector a b) := by
  constructor
  · simp [topCoordinateProjector, fromBlocks_transpose]
  · simp [topCoordinateProjector, fromBlocks_multiply]

theorem topCoordinateProjector_complement :
    1 - topCoordinateProjector a b = fromBlocks (0 : Matrix a a ℝ) 0 0 (1 : Matrix b b ℝ) := by
  ext i j
  cases i <;> cases j <;> simp [topCoordinateProjector, Matrix.one_apply]

theorem bottom_block_compression (M : Matrix (a ⊕ b) (a ⊕ b) ℝ) :
    (1 - topCoordinateProjector a b) * M * (1 - topCoordinateProjector a b) =
      fromBlocks (0 : Matrix a a ℝ) 0 0 (M.submatrix Sum.inr Sum.inr) := by
  rw [topCoordinateProjector_complement]
  conv_lhs => arg 1; arg 2; rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply, Matrix.toBlocks₂₂, Matrix.submatrix]

theorem zero_top_block_posSemidef {D : Matrix b b ℝ} (hD : D.PosSemidef) :
    (fromBlocks (0 : Matrix a a ℝ) 0 0 D).PosSemidef := by
  constructor
  · simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial,
      fromBlocks_transpose, transpose_zero] using
        congrArg (fun E : Matrix b b ℝ => fromBlocks (0 : Matrix a a ℝ) 0 0 E)
          (show Dᵀ = D by simpa only [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq)
  · intro v
    have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext i; cases i <;> rfl
    rw [hv]
    simpa only [star_trivial, fromBlocks_mulVec, Function.comp_def, Sum.elim_inl,
      Sum.elim_inr, zero_mulVec, zero_add, add_zero, sumElim_dotProduct_sumElim,
      dotProduct_zero, zero_add] using hD.2 (v ∘ Sum.inr)

theorem bottom_block_loewner_compression {M : Matrix (a ⊕ b) (a ⊕ b) ℝ} {c : ℝ}
    (hbottom : LoewnerLE (M.submatrix Sum.inr Sum.inr) (c • (1 : Matrix b b ℝ))) :
    LoewnerLE ((1 - topCoordinateProjector a b) * M * (1 - topCoordinateProjector a b))
      (c • (1 - topCoordinateProjector a b)) := by
  rw [bottom_block_compression, topCoordinateProjector_complement]
  have he : c • fromBlocks (0 : Matrix a a ℝ) 0 0 (1 : Matrix b b ℝ) -
      fromBlocks (0 : Matrix a a ℝ) 0 0 (M.submatrix Sum.inr Sum.inr) =
      fromBlocks (0 : Matrix a a ℝ) 0 0 (c • (1 : Matrix b b ℝ) - M.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i <;> cases j <;> simp
  unfold LoewnerLE
  rw [he]
  exact zero_top_block_posSemidef a b hbottom

theorem topCoordinateProjector_trace_mul (M : Matrix (a ⊕ b) (a ⊕ b) ℝ) :
    (topCoordinateProjector a b * M).trace = (M.submatrix Sum.inl Sum.inl).trace := by
  conv_lhs => arg 1; arg 2; rw [← fromBlocks_toBlocks M]
  simp [topCoordinateProjector, fromBlocks_multiply, Matrix.trace, Matrix.diag,
    Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.submatrix]

theorem posterior_trace_bound_of_bottom {M P : Matrix (a ⊕ b) (a ⊕ b) ℝ} {c : ℝ}
    (hM : M.PosSemidef) (hP : IsOrthogonalProjector P) (hc : 0 ≤ c)
    (hbottom : LoewnerLE (M.submatrix Sum.inr Sum.inr) (c • (1 : Matrix b b ℝ))) :
    (P * M).trace ≤ 2 * (M.submatrix Sum.inl Sum.inl).trace + 2 * c * P.trace := by
  have h := posterior_trace_bound hM (topCoordinateProjector_isProjector a b) hP hc
    (bottom_block_loewner_compression a b hbottom)
  simpa only [topCoordinateProjector_trace_mul] using h

end
end LowRank
