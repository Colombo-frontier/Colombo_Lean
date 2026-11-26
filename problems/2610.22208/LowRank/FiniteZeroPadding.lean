import LowRank.SchattenPaddingOptimum

/-! The concrete top-left zero padding of finite rectangular matrices.
Its two-sided matvec formulas and relative Schatten guarantee follow from
the isometric embedding results. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def coordinateEmbedding {d a : ℕ} (h : d ≤ a) : Matrix (Fin a) (Fin d) ℝ :=
  (1 : Matrix (Fin a) (Fin a) ℝ).submatrix id (Fin.castLE h)

theorem coordinateEmbedding_orthogonal {d a : ℕ} (h : d ≤ a) :
    (coordinateEmbedding h)ᵀ * coordinateEmbedding h = 1 := by
  have heq := compressed_submatrix (1 : Matrix (Fin a) (Fin a) ℝ)
    (1 : Matrix (Fin a) (Fin a) ℝ) (Fin.castLE h)
  simpa only [coordinateEmbedding, Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.submatrix_one _ (Fin.castLE_injective h)] using heq

theorem coordinateEmbedding_transpose_mulVec {d a : ℕ} (h : d ≤ a) (v : Fin a → ℝ) :
    (coordinateEmbedding h)ᵀ *ᵥ v = fun i => v (i.castLE h) := by
  ext i
  simp [coordinateEmbedding, Matrix.mulVec, dotProduct, Matrix.submatrix,
    Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem coordinateEmbedding_mulVec {d a : ℕ} (h : d ≤ a) (v : Fin d → ℝ) (i : Fin a) :
    (coordinateEmbedding h *ᵥ v) i = if hi : i.val < d then v ⟨i.val, hi⟩ else 0 := by
  by_cases hi : i.val < d
  · rw [dif_pos hi]
    simp only [coordinateEmbedding, Matrix.mulVec, dotProduct, Matrix.submatrix,
      id_eq, Matrix.one_apply]
    rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin d)]
    · simp
    · intro j _ hj
      have hij : i ≠ j.castLE h := by
        intro heq
        apply hj
        apply Fin.ext
        exact (congrArg Fin.val heq).symm
      simp [hij]
    · simp
  · rw [dif_neg hi]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    change (if i = j.castLE h then 1 else 0) * v j = 0
    have hij : i ≠ j.castLE h := by
      intro heq
      apply hi
      have hval := congrArg Fin.val heq
      simpa only [hval] using j.isLt
    simp [hij]

def zeroPadFin {a b d t : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) : Matrix (Fin a) (Fin b) ℝ :=
  coordinateEmbedding hm * A * (coordinateEmbedding hn)ᵀ

theorem zeroPadFin_matvec {a b d t : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) (v : Fin b → ℝ) :
    zeroPadFin hm hn A *ᵥ v =
      coordinateEmbedding hm *ᵥ (A *ᵥ (fun j => v (j.castLE hn))) := by
  simp only [zeroPadFin, ← Matrix.mulVec_mulVec, coordinateEmbedding_transpose_mulVec]

theorem zeroPadFin_transpose_matvec {a b d t : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) (v : Fin a → ℝ) :
    (zeroPadFin hm hn A)ᵀ *ᵥ v =
      coordinateEmbedding hn *ᵥ (Aᵀ *ᵥ (fun i => v (i.castLE hm))) := by
  simp only [zeroPadFin, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mulVec_mulVec, coordinateEmbedding_transpose_mulVec]

theorem zeroPadFin_schattenNorm {a b d t : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm p (zeroPadFin hm hn A) = schattenNorm p A :=
  schattenNorm_isometric_embedding hp _ (coordinateEmbedding_orthogonal hm)
    _ (coordinateEmbedding_orthogonal hn) A

theorem zeroPadFin_optimalSchattenNorm {a b d t k : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) {p : ℝ} (hp : 0 < p) :
    optimalSchattenNorm p (zeroPadFin hm hn A) k = optimalSchattenNorm p A k :=
  optimalSchattenNorm_isometric_embedding hp _ (coordinateEmbedding_orthogonal hm)
    _ (coordinateEmbedding_orthogonal hn) A hk

theorem zeroPadFin_relative_guarantee {a b d t k : ℕ} (hm : d ≤ a) (hn : t ≤ b)
    (A : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) {p ε : ℝ} (hp : 0 < p)
    (Z : Matrix (Fin b) (Fin k) ℝ)
    (hsuccess : schattenNorm p (zeroPadFin hm hn A * (1 - Z * Zᵀ)) ≤
      (1 + ε) * optimalSchattenNorm p (zeroPadFin hm hn A) k) :
    IsOrthogonalProjector (truncatedColumnProjector (coordinateEmbedding hn) Z) ∧
      (truncatedColumnProjector (coordinateEmbedding hn) Z).rank ≤ k ∧
      schattenNorm p (A * (1 - truncatedColumnProjector (coordinateEmbedding hn) Z)) ≤
        (1 + ε) * optimalSchattenNorm p A k :=
  relative_schatten_truncation hp _ (coordinateEmbedding_orthogonal hm)
    _ (coordinateEmbedding_orthogonal hn) A hk Z hsuccess

end
end LowRank
