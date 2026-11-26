import LowRank.JoinedOrthogonalColumns
import LowRank.UnorderedDiagonalization

/-! Isometric extension only adds zero eigenvalues. For positive powers,
it preserves the spectral power sum. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem symmetricPowerTrace_eq_of_reindexed_diagonalization {d : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    (e : Fin d ≃ ι) (lam : ι → ℝ) (J : Matrix (Fin d) ι ℝ)
    (hJ : Jᵀ * J = 1) (hdiag : Jᵀ * M * J = diagonal lam) (r : ℝ) :
    symmetricPowerTrace hM r = ∑ i, lam i ^ r := by
  let U := J.submatrix id e
  have hU : Uᵀ * U = 1 := by
    change Jᵀ.submatrix e id * J.submatrix id e = 1
    have h := Matrix.submatrix_mul_equiv Jᵀ J e (Equiv.refl (Fin d)) e
    simpa only [Equiv.coe_refl, hJ, Matrix.submatrix_one_equiv] using h
  have hUd : Uᵀ * M * U = diagonal (lam ∘ e) := by
    change Jᵀ.submatrix e id * M * J.submatrix id e = diagonal (lam ∘ e)
    have hfirst : Jᵀ.submatrix e id * M = (Jᵀ * M).submatrix e id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Jᵀ M e (Equiv.refl (Fin d)) id
    rw [hfirst]
    have h := Matrix.submatrix_mul_equiv (Jᵀ * M) J e (Equiv.refl (Fin d)) e
    simpa only [Equiv.coe_refl, hdiag, Matrix.submatrix_diagonal_equiv] using h
  rw [symmetricPowerTrace_eq_of_diagonalization hM (lam ∘ e) U hU hUd r]
  exact e.sum_comp (fun i => lam i ^ r)

theorem extension_isHermitian {d m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.IsHermitian) (B : Matrix (Fin d) (Fin m) ℝ) : (B * C * Bᵀ).IsHermitian := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose B hC

theorem symmetricPowerTrace_isometric_extension {k m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.IsHermitian)
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    {r : ℝ} (hr : 0 < r) :
    symmetricPowerTrace (extension_isHermitian hC B) r = symmetricPowerTrace hC r := by
  obtain ⟨A, hA, _, hAB⟩ := exists_orthogonal_complement_columns B hB
  let sp := orderedMatrixSpectrum hC
  let E := B * sp.basis
  let D := B * C * Bᵀ
  have hBA : Bᵀ * A = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hAB
  have hE : Eᵀ * E = 1 := by
    calc
      _ = sp.basisᵀ * (Bᵀ * B) * sp.basis := by
        simp only [E, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB, Matrix.mul_one, sp.orthogonal]
  have hAE : Aᵀ * E = 0 := by
    dsimp [E]
    rw [← Matrix.mul_assoc, hAB, Matrix.zero_mul]
  have hEA : Eᵀ * A = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hAE
  have hAD : Aᵀ * D = 0 := by
    calc
      _ = (Aᵀ * B) * C * Bᵀ := by simp only [D, Matrix.mul_assoc]
      _ = 0 := by rw [hAB, Matrix.zero_mul, Matrix.zero_mul]
  have hDA : D * A = 0 := by
    simp only [D, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hEDE : Eᵀ * D * E = diagonal sp.value := by
    calc
      _ = sp.basisᵀ * (Bᵀ * B) * C * (Bᵀ * B) * sp.basis := by
        simp only [E, D, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one, Matrix.mul_one, sp.diagonalizes]
  have hJ : (joinColumns A E)ᵀ * joinColumns A E = 1 := by
    rw [joinColumns_gram, hA, hAE, hEA, hE]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hJd : (joinColumns A E)ᵀ * D * joinColumns A E =
      diagonal (Sum.elim (fun _ : Fin k => (0 : ℝ)) sp.value) := by
    rw [joinColumns_compression, hAD, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.mul_assoc Eᵀ D A, hDA, Matrix.mul_zero, hEDE]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.diagonal]
  have h := symmetricPowerTrace_eq_of_reindexed_diagonalization (extension_isHermitian hC B)
    finSumFinEquiv.symm (Sum.elim (fun _ : Fin k => (0 : ℝ)) sp.value)
    (joinColumns A E) hJ hJd r
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Real.zero_rpow (ne_of_gt hr), Finset.sum_const_zero, zero_add, sp,
    symmetricPowerTrace] using h

end
end LowRank
