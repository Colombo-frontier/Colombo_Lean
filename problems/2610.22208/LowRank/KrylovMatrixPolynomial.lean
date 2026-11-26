import LowRank.KrylovCompression
import LowRank.ChebyshevGapFilter
import LowRank.OrderedMatrixSpectrum
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Polynomial evaluation on the actual Gram matrix. Orthogonal spectral
coordinates evaluate the polynomial entrywise, and a polynomial of degree
below the number of Krylov blocks is represented in the queried subspace. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix BigOperators
noncomputable section

theorem OrderedMatrixSpectrum.diagonalizes_pow {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (n : ℕ) :
    sp.basisᵀ * A ^ n * sp.basis = diagonal (fun i => sp.value i ^ n) := by
  induction n with
  | zero => simpa using sp.orthogonal
  | succ n ih =>
      calc
        _ = sp.basisᵀ * A ^ n * (sp.basis * sp.basisᵀ) * A * sp.basis := by
          rw [sp.orthogonal_right, Matrix.mul_one, pow_succ]
          noncomm_ring
        _ = (sp.basisᵀ * A ^ n * sp.basis) * (sp.basisᵀ * A * sp.basis) := by noncomm_ring
        _ = _ := by
          rw [ih, sp.diagonalizes, diagonal_mul_diagonal]
          congr 1

theorem OrderedMatrixSpectrum.diagonalizes_aeval {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (f : ℝ[X]) :
    sp.basisᵀ * aeval A f * sp.basis = diagonal (fun i => f.eval (sp.value i)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, Matrix.mul_add, Matrix.add_mul, hf, hg, eval_add, ← diagonal_add]
  | monomial n r =>
      rw [aeval_monomial, ← Algebra.smul_def, Matrix.mul_smul, Matrix.smul_mul,
        sp.diagonalizes_pow, ← diagonal_smul]
      simp only [eval_monomial]
      rfl

theorem OrderedMatrixSpectrum.aeval_mul_basis {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (f : ℝ[X]) :
    aeval A f * sp.basis = sp.basis * diagonal (fun i => f.eval (sp.value i)) := by
  have h := congrArg (fun B => sp.basis * B) (sp.diagonalizes_aeval f)
  simpa only [← Matrix.mul_assoc, sp.orthogonal_right, Matrix.one_mul] using h

theorem OrderedMatrixSpectrum.aeval_reconstruct {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (f : ℝ[X]) :
    aeval A f = sp.basis * diagonal (fun i => f.eval (sp.value i)) * sp.basisᵀ := by
  rw [← sp.aeval_mul_basis, Matrix.mul_assoc, sp.orthogonal_right, Matrix.mul_one]

theorem krylovProjector_fixes_aeval {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin a) (Fin s) ℝ) (f : ℝ[X]) (hf : f.natDegree < n) :
    columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) *
        (aeval (Aᵀ * A) f * (Aᵀ * U)) = aeval (Aᵀ * A) f * (Aᵀ * U) := by
  have heq : aeval (Aᵀ * A) f * (Aᵀ * U) =
      ∑ i : Fin n, f.coeff i.val • ((Aᵀ * A) ^ i.val * (Aᵀ * U)) := by
    rw [aeval_eq_sum_range' hf, Matrix.sum_mul]
    simpa only [Matrix.smul_mul] using
      (Fin.sum_univ_eq_sum_range (fun j => f.coeff j • ((Aᵀ * A) ^ j * (Aᵀ * U))) n).symm
  rw [heq]
  exact krylovProjector_fixes_polynomial A U (fun i => f.coeff i.val)

theorem krylovProjector_fixes_chebyshevFilter {a b s : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) (t γ η : ℝ) :
    let n := chebyshevFilterDegree γ η + 1
    let f := chebyshevGapFilter t γ (chebyshevFilterDegree γ η)
    columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) *
        (aeval (Aᵀ * A) f * (Aᵀ * U)) = aeval (Aᵀ * A) f * (Aᵀ * U) := by
  apply krylovProjector_fixes_aeval
  exact Nat.lt_succ_of_le (chebyshevGapFilter_natDegree_le _ _ _)

end
end LowRank
