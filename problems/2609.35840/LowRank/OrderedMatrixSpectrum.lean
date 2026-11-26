import LowRank.AdaptedQuadratic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Fin.Tuple.Sort

/-! Real symmetric matrices have an orthogonal diagonalization with
eigenvalues in increasing order. The order is chosen explicitly by a finite
permutation of Mathlib's spectral basis. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

structure OrderedMatrixSpectrum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) where
  value : Fin d → ℝ
  basis : Matrix (Fin d) (Fin d) ℝ
  increasing : Monotone value
  orthogonal : basisᵀ * basis = 1
  diagonalizes : basisᵀ * A * basis = Matrix.diagonal value

theorem OrderedMatrixSpectrum.orthogonal_right {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : sp.basis * sp.basisᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp sp.orthogonal

def orderedMatrixSpectrum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    OrderedMatrixSpectrum A := by
  let U : Matrix (Fin d) (Fin d) ℝ := hA.eigenvectorUnitary
  let σ := Tuple.sort hA.eigenvalues
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff').mp hA.eigenvectorUnitary.2
  have hdiag : Uᵀ * A * U = diagonal hA.eigenvalues := by
    simpa only [U, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      Function.comp_def] using hA.star_mul_self_mul_eq_diagonal
  refine ⟨hA.eigenvalues ∘ σ, U.submatrix id σ, Tuple.monotone_sort _, ?_, ?_⟩
  · change Uᵀ.submatrix σ id * U.submatrix id σ = 1
    have h := Matrix.submatrix_mul_equiv Uᵀ U σ (Equiv.refl (Fin d)) σ
    simpa only [Equiv.coe_refl, hU, Matrix.submatrix_one_equiv] using h
  · change Uᵀ.submatrix σ id * A * U.submatrix id σ = diagonal (hA.eigenvalues ∘ σ)
    have hfirst : Uᵀ.submatrix σ id * A = (Uᵀ * A).submatrix σ id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Uᵀ A σ (Equiv.refl (Fin d)) id
    rw [hfirst]
    have h := Matrix.submatrix_mul_equiv (Uᵀ * A) U σ (Equiv.refl (Fin d)) σ
    simpa only [Equiv.coe_refl, hdiag, Matrix.submatrix_diagonal_equiv] using h

theorem OrderedMatrixSpectrum.reconstruct {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : A = sp.basis * diagonal sp.value * sp.basisᵀ := by
  rw [← sp.diagonalizes]
  calc
    A = (sp.basis * sp.basisᵀ) * A * (sp.basis * sp.basisᵀ) := by rw [sp.orthogonal_right]; simp
    _ = sp.basis * (sp.basisᵀ * A * sp.basis) * sp.basisᵀ := by noncomm_ring

theorem OrderedMatrixSpectrum.trace {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) : A.trace = ∑ i, sp.value i := by
  have h := congrArg Matrix.trace sp.diagonalizes
  rw [Matrix.trace_mul_cycle, sp.orthogonal_right, one_mul, Matrix.trace_diagonal] at h
  exact h

theorem OrderedMatrixSpectrum.quadratic {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (x : Fin d → ℝ) :
    (sp.basis *ᵥ x) ⬝ᵥ (A *ᵥ (sp.basis *ᵥ x)) = ∑ i, sp.value i * (x i) ^ 2 := by
  rw [quadratic_coordinates, sp.diagonalizes]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem orthogonal_columns_dot {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (B : Matrix a b ℝ) (hB : Bᵀ * B = 1) (x : b → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ x := by
  classical
  have h := quadratic_coordinates B (1 : Matrix a a ℝ) x
  simpa only [one_mulVec, Matrix.mul_one, hB] using h

theorem OrderedMatrixSpectrum.value_mem_Icc {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) {a b : ℝ}
    (hlow : LoewnerLE (a • 1) A) (hupp : LoewnerLE A (b • 1)) (i : Fin d) :
    sp.value i ∈ Set.Icc a b := by
  have hl := loewner_congruence hlow sp.basis
  have hu := loewner_congruence hupp sp.basis
  simp only [sp.diagonalizes, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, sp.orthogonal] at hl hu
  have hl' := psd_diagonal_nonneg hl i
  have hu' := psd_diagonal_nonneg hu i
  simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_nonneg] using And.intro hl' hu'

end
end LowRank
