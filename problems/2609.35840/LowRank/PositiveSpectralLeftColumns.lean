import LowRank.WeightedFilteredApproximation
import LowRank.GaussianMatrixCompression

/-! Positive right-Gram spectral columns give orthonormal left directions.
They identify the actual starting block with a scaled iid Gaussian matrix. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def positiveSpectralLeftColumns {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin k → Fin b) : Matrix (Fin a) (Fin k) ℝ :=
  A * sp.basis.submatrix id f * diagonal (fun j => (Real.sqrt (sp.value (f j)))⁻¹)

theorem spectral_subcolumns_gram {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin k → Fin b) (hf : Function.Injective f) :
    (A * sp.basis.submatrix id f)ᵀ * (A * sp.basis.submatrix id f) =
      diagonal (fun j => sp.value (f j)) := by
  calc
    _ = (sp.basis.submatrix id f)ᵀ * (Aᵀ * A) * sp.basis.submatrix id f := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [compressed_submatrix, sp.diagonalizes, Matrix.submatrix_diagonal _ _ hf]
      rfl

theorem positiveSpectralLeftColumns_orthogonal {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin k → Fin b) (hf : Function.Injective f)
    (hp : ∀ j, 0 < sp.value (f j)) :
    (positiveSpectralLeftColumns A sp f)ᵀ * positiveSpectralLeftColumns A sp f = 1 := by
  have hg := spectral_subcolumns_gram A sp f hf
  calc
    _ = diagonal (fun j => (Real.sqrt (sp.value (f j)))⁻¹) *
        ((A * sp.basis.submatrix id f)ᵀ * (A * sp.basis.submatrix id f)) *
          diagonal (fun j => (Real.sqrt (sp.value (f j)))⁻¹) := by
      simp only [positiveSpectralLeftColumns, Matrix.transpose_mul, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
    _ = _ := by
      rw [hg, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      have he (j : Fin k) :
          (Real.sqrt (sp.value (f j)))⁻¹ * sp.value (f j) * (Real.sqrt (sp.value (f j)))⁻¹ = 1 := by
        have hs := Real.sq_sqrt (hp j).le
        have hn : Real.sqrt (sp.value (f j)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp j))
        field_simp
      simp only [he, Matrix.diagonal_one]

theorem spectral_startingBlock_factor {a b k s : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin k → Fin b)
    (hp : ∀ j, 0 < sp.value (f j)) (U : Matrix (Fin a) (Fin s) ℝ) :
    (sp.basisᵀ * (Aᵀ * U)).submatrix f id =
      diagonal (fun j => Real.sqrt (sp.value (f j))) * ((positiveSpectralLeftColumns A sp f)ᵀ * U) := by
  have hinv := diagonal_mul_reciprocal (fun j => Real.sqrt (sp.value (f j)))
    (fun j => ne_of_gt (Real.sqrt_pos.mpr (hp j)))
  have hsub : (sp.basisᵀ * (Aᵀ * U)).submatrix f id =
      (sp.basis.submatrix id f)ᵀ * (Aᵀ * U) := by
    ext i j
    rfl
  rw [hsub]
  simp only [positiveSpectralLeftColumns, Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem iidMatrixLaw_spectral_left_coordinates {a b k s : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin k → Fin b) (hf : Function.Injective f) (hp : ∀ j, 0 < sp.value (f j)) (v : NNReal) :
    (iidMatrixLaw a s v).map (fun U => (positiveSpectralLeftColumns A sp f)ᵀ * U) =
      iidMatrixLaw k s v :=
  iidMatrixLaw_left_compression _ (positiveSpectralLeftColumns_orthogonal A sp f hf hp) v

end
end LowRank
