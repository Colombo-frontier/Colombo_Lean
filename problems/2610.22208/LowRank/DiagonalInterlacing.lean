import LowRank.OrderedMatrixSpectrum

/-! Eigenvalue separation for a diagonal quadratic form compressed by an
isometric embedding. A dimension argument supplies a nonzero vector whose
first coordinates vanish; no min-max principle is assumed. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem short_matrix_has_nonzero_kernel (a b : ℕ) (hab : a < b)
    (M : Matrix (Fin a) (Fin b) ℝ) : ∃ x : Fin b → ℝ, M *ᵥ x = 0 ∧ x ≠ 0 := by
  have h : LinearMap.ker M.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hab)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
  exact ⟨x, hx, hx0⟩

theorem compressed_submatrix {d m a : ℕ} (B : Matrix (Fin d) (Fin m) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin a → Fin m) :
    (B.submatrix id c)ᵀ * A * B.submatrix id c = (Bᵀ * A * B).submatrix c c := by
  have hfirst : (B.submatrix id c)ᵀ * A = (Bᵀ * A).submatrix c id := by
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv Bᵀ A c (Equiv.refl (Fin d)) id
  rw [hfirst]
  simpa only [Equiv.coe_refl] using
    Matrix.submatrix_mul_equiv (Bᵀ * A) B c (Equiv.refl (Fin d)) c

theorem diagonal_quadratic (d : ℕ) (lam x : Fin d → ℝ) :
    x ⬝ᵥ (diagonal lam *ᵥ x) = ∑ j, lam j * (x j) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dot_self_eq_sum_sq {d : ℕ} (x : Fin d → ℝ) : x ⬝ᵥ x = ∑ j, (x j) ^ 2 := by
  simp only [dotProduct, pow_two]

theorem diagonal_compression_eigenvalue_le_of_loewner {d m : ℕ} (hm : m ≤ d)
    (lam : Fin d → ℝ) (θ : Fin m → ℝ) (hlam : Monotone lam) (hθ : Monotone θ)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hdiag : LoewnerLE (Bᵀ * diagonal lam * B) (diagonal θ)) (i : Fin m) :
    lam (i.castLE hm) ≤ θ i := by
  let c : Fin (i.val + 1) → Fin m := Fin.castLE (Nat.succ_le_of_lt i.isLt)
  let T := B.submatrix id c
  have hc : Function.Injective c := Fin.castLE_injective _
  have hT : Tᵀ * T = 1 := by
    have h := compressed_submatrix B (1 : Matrix (Fin d) (Fin d) ℝ) c
    simpa only [Matrix.mul_one, hB, Matrix.submatrix_one _ hc] using h
  have hTd : LoewnerLE (Tᵀ * diagonal lam * T) (diagonal (θ ∘ c)) := by
    have h := hdiag.submatrix c
    simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_diagonal _ _ hc,
      ← compressed_submatrix] using h
  let a : Fin i.val → Fin d := Fin.castLE (le_trans (Nat.le_of_lt i.isLt) hm)
  obtain ⟨x, hx, hx0⟩ := short_matrix_has_nonzero_kernel i.val (i.val + 1)
    (Nat.lt_succ_self _) (T.submatrix a id)
  let y := T *ᵥ x
  have hy : ∀ j : Fin d, j.val < i.val → y j = 0 := by
    intro j hj
    have h := congrFun hx (⟨j.val, hj⟩ : Fin i.val)
    exact h
  have hnorm : y ⬝ᵥ y = x ⬝ᵥ x := orthogonal_columns_dot T hT x
  have hpos : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hx0)
  have hlow : lam (i.castLE hm) * (y ⬝ᵥ y) ≤ y ⬝ᵥ (diagonal lam *ᵥ y) := by
    rw [diagonal_quadratic, dot_self_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j.val < i.val
    · simp only [hy j hj, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hlam (by exact Nat.le_of_not_gt hj)) (sq_nonneg _)
  have hupp : y ⬝ᵥ (diagonal lam *ᵥ y) ≤ θ i * (x ⬝ᵥ x) := by
    calc
      _ = x ⬝ᵥ ((Tᵀ * diagonal lam * T) *ᵥ x) := quadratic_coordinates _ _ _
      _ ≤ x ⬝ᵥ (diagonal (θ ∘ c) *ᵥ x) := loewner_quadratic_le hTd x
      _ ≤ θ i * (x ⬝ᵥ x) := by
        rw [diagonal_quadratic, dot_self_eq_sum_sq, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hθ (by exact Nat.le_of_lt_succ j.isLt)) (sq_nonneg _)
  rw [hnorm] at hlow
  exact (mul_le_mul_right hpos).mp (hlow.trans hupp)

theorem diagonal_compression_eigenvalue_le {d m : ℕ} (hm : m ≤ d)
    (lam : Fin d → ℝ) (θ : Fin m → ℝ) (hlam : Monotone lam) (hθ : Monotone θ)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hdiag : Bᵀ * diagonal lam * B = diagonal θ) (i : Fin m) :
    lam (i.castLE hm) ≤ θ i := by
  apply diagonal_compression_eigenvalue_le_of_loewner hm lam θ hlam hθ B hB _ i
  rw [LoewnerLE, hdiag, sub_self]
  exact Matrix.PosSemidef.zero

end
end LowRank

