import LowRank.MeasurableOptimalColumns
import LowRank.ProjectionApproximation

/-! The algorithm's measurable optimal columns are explicit spectral
columns. Nonzero eigenvectors of a compressed Gram matrix lie in the
query subspace; zero eigenvalues are treated separately. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem OrderedMatrixSpectrum.mul_column {b : ℕ} {H : Matrix (Fin b) (Fin b) ℝ}
    (sp : OrderedMatrixSpectrum H) (j : Fin b) :
    H *ᵥ (fun i => sp.basis i j) = sp.value j • (fun i => sp.basis i j) := by
  funext i
  have h := congrFun (congrFun sp.mul_basis i) j
  rw [Matrix.mul_diagonal] at h
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem compressed_eigenvector_fixed {b : ℕ} {P H : Matrix (Fin b) (Fin b) ℝ}
    (hPH : P * H = H) (z : Fin b → ℝ) {e : ℝ} (hz : H *ᵥ z = e • z) (he : e ≠ 0) :
    P *ᵥ z = z := by
  have h := congrArg (fun x => P *ᵥ x) hz
  dsimp only at h
  rw [Matrix.mulVec_mulVec, hPH, hz, Matrix.mulVec_smul] at h
  funext i
  have hi := congrFun h i
  exact mul_left_cancel₀ he hi.symm

theorem projector_mul_compressedGram {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P) :
    P * ((A * P)ᵀ * (A * P)) = (A * P)ᵀ * (A * P) := by
  simp only [Matrix.transpose_mul, hP.symmetric, ← Matrix.mul_assoc, hP.idempotent]

theorem spectral_subcolumns_mul {b k : ℕ} {H : Matrix (Fin b) (Fin b) ℝ}
    (sp : OrderedMatrixSpectrum H) (f : Fin k → Fin b) :
    H * sp.basis.submatrix id f = sp.basis.submatrix id f * diagonal (fun j => sp.value (f j)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrFun (sp.mul_column (f j)) i
  simpa only [Matrix.mul_diagonal, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
    Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem optimalColumnSelector_gram_eigenvectors {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (Aᵀ * A) * optimalColumnSelector a b k hk A =
      optimalColumnSelector a b k hk A * diagonal
        (fun j => (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j)) :=
  spectral_subcolumns_mul (canonicalOrderedSpectrum b (symmetricRightGram A)) _

theorem optimalColumnSelector_compressed_column_fixed {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P)
    (j : Fin k)
    (hj : (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value (lastColumnIndex b k hk j) ≠ 0) :
    P *ᵥ (fun i => optimalColumnSelector a b k hk (A * P) i j) =
      fun i => optimalColumnSelector a b k hk (A * P) i j := by
  exact compressed_eigenvector_fixed (projector_mul_compressedGram A hP) _
    ((canonicalOrderedSpectrum b (symmetricRightGram (A * P))).mul_column _) hj

end
end LowRank
