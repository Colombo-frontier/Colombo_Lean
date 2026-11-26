import LowRank.SpectralPowers

/-! A spectral power sum can be evaluated in any orthogonal eigenbasis;
the input diagonal need not be sorted. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def orderedSpectrumOfDiagonalization {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (lam : Fin d → ℝ) (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (hdiag : Uᵀ * A * U = diagonal lam) :
    OrderedMatrixSpectrum A := by
  let σ := Tuple.sort lam
  refine ⟨lam ∘ σ, U.submatrix id σ, Tuple.monotone_sort _, ?_, ?_⟩
  · change Uᵀ.submatrix σ id * U.submatrix id σ = 1
    have h := Matrix.submatrix_mul_equiv Uᵀ U σ (Equiv.refl (Fin d)) σ
    simpa only [Equiv.coe_refl, hU, Matrix.submatrix_one_equiv] using h
  · change Uᵀ.submatrix σ id * A * U.submatrix id σ = diagonal (lam ∘ σ)
    have hfirst : Uᵀ.submatrix σ id * A = (Uᵀ * A).submatrix σ id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Uᵀ A σ (Equiv.refl (Fin d)) id
    rw [hfirst]
    have h := Matrix.submatrix_mul_equiv (Uᵀ * A) U σ (Equiv.refl (Fin d)) σ
    simpa only [Equiv.coe_refl, hdiag, Matrix.submatrix_diagonal_equiv] using h

theorem symmetricPowerTrace_eq_of_diagonalization {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (lam : Fin d → ℝ) (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (hdiag : Uᵀ * A * U = diagonal lam) (r : ℝ) :
    symmetricPowerTrace hA r = ∑ i, lam i ^ r := by
  rw [symmetricPowerTrace_eq hA (orderedSpectrumOfDiagonalization lam U hU hdiag) r]
  exact Equiv.sum_comp (Tuple.sort lam) (fun i => lam i ^ r)

theorem OrderedMatrixSpectrum.mul_basis {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : A * sp.basis = sp.basis * diagonal sp.value := by
  calc
    A * sp.basis = (sp.basis * sp.basisᵀ) * A * sp.basis := by
      rw [sp.orthogonal_right, one_mul]
    _ = sp.basis * (sp.basisᵀ * A * sp.basis) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [sp.diagonalizes]

end
end LowRank
