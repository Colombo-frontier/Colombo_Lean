import LowRank.BlockReveal
import LowRank.GaussianGaugeMatrix

/-! Extend a local orthogonal gauge by the identity on previously exposed
coordinates, and update possibly differently indexed full orthogonal bases. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def extendGauge {a b : Type*} [DecidableEq a] (T : Matrix b b ℝ) :
    Matrix (a ⊕ b) (a ⊕ b) ℝ := fromBlocks 1 0 0 T

theorem extendGauge_transpose_mul {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (T : Matrix b b ℝ) (hT : Tᵀ * T = 1) :
    (extendGauge (a := a) T)ᵀ * extendGauge T = 1 := by
  simp [extendGauge, fromBlocks_transpose, fromBlocks_multiply, hT, fromBlocks_one]

theorem extendGauge_mul_transpose {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (T : Matrix b b ℝ) (hT : T * Tᵀ = 1) :
    extendGauge (a := a) T * (extendGauge T)ᵀ = 1 := by
  simp [extendGauge, fromBlocks_transpose, fromBlocks_multiply, hT, fromBlocks_one]

def changedBasis {m n o : Type*} [Fintype n] (B : Matrix m n ℝ) (L : Matrix n n ℝ)
    (e : o ≃ n) : Matrix m o ℝ := (B * Lᵀ).submatrix id e

theorem changedBasis_transpose_mul {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o] (B : Matrix m n ℝ) (L : Matrix n n ℝ) (e : o ≃ n)
    (hB : Bᵀ * B = 1) (hL : L * Lᵀ = 1) :
    (changedBasis B L e)ᵀ * changedBasis B L e = 1 := by
  simp only [changedBasis, transpose_submatrix, transpose_mul, transpose_transpose]
  have hm := submatrix_mul_equiv (L * Bᵀ) (B * Lᵀ) e (Equiv.refl m) e
  simp only [Equiv.coe_refl] at hm
  rw [hm]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ B Lᵀ, hB, Matrix.one_mul, hL]
  exact submatrix_one_equiv e

theorem changedBasis_mul_transpose {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    [DecidableEq m] [DecidableEq n] (B : Matrix m n ℝ) (L : Matrix n n ℝ) (e : o ≃ n)
    (hB : B * Bᵀ = 1) (hL : Lᵀ * L = 1) :
    changedBasis B L e * (changedBasis B L e)ᵀ = 1 := by
  simp only [changedBasis, transpose_submatrix, transpose_mul, transpose_transpose]
  rw [submatrix_mul_equiv _ _ id e id, submatrix_id_id]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ L Bᵀ, hL, Matrix.one_mul, hB]

theorem changedBasis_reconstruct {m n p t a b : Type*}
    [Fintype n] [Fintype p] [Fintype a] [Fintype b] [DecidableEq n] [DecidableEq p]
    (B : Matrix m n ℝ) (V : Matrix t p ℝ) (X : Matrix n p ℝ)
    (L : Matrix n n ℝ) (R : Matrix p p ℝ) (er : a ≃ n) (ec : b ≃ p)
    (hL : Lᵀ * L = 1) (hR : Rᵀ * R = 1) :
    changedBasis B L er * (L * X * Rᵀ).submatrix er ec * (changedBasis V R ec)ᵀ =
      B * X * Vᵀ := by
  simp only [changedBasis, transpose_submatrix, transpose_mul, transpose_transpose]
  rw [submatrix_mul_equiv _ _ id er ec, submatrix_mul_equiv _ _ id ec id, submatrix_id_id]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc B Lᵀ L, hL, Matrix.mul_one]
  rw [Matrix.mul_assoc (B * X) Rᵀ R, hR, Matrix.mul_one]

end
end LowRank
