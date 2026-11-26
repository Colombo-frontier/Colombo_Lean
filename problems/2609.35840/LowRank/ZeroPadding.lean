import LowRank.MatrixOrder
import Mathlib.Data.Matrix.Block

/-! Correctly typed zero-padding identities. In particular the padded residual
Gram matrix has an additional zero block; it is not literally the smaller Gram matrix. -/

namespace LowRank
open Matrix
open scoped Matrix

variable {a r c : Type*} [Fintype a] [Fintype r] [Fintype c]
  [DecidableEq a] [DecidableEq r] [DecidableEq c]

def zeroPad (A : Matrix a a ℝ) : Matrix (a ⊕ r) (a ⊕ c) ℝ := fromBlocks A 0 0 0

theorem padded_matvec (A : Matrix a a ℝ) (v : a ⊕ c → ℝ) :
    (zeroPad A : Matrix (a ⊕ r) (a ⊕ c) ℝ) *ᵥ v =
      Sum.elim (A *ᵥ (v ∘ Sum.inl)) 0 := by
  simp [zeroPad, fromBlocks_mulVec]

theorem padded_transpose_matvec (A : Matrix a a ℝ) (v : a ⊕ r → ℝ) :
    (zeroPad A : Matrix (a ⊕ r) (a ⊕ c) ℝ)ᵀ *ᵥ v =
      Sum.elim (Aᵀ *ᵥ (v ∘ Sum.inl)) 0 := by
  simp [zeroPad, fromBlocks_transpose, fromBlocks_mulVec]

theorem padded_residual_gram (A P₁₁ : Matrix a a ℝ)
    (P₁₂ : Matrix a c ℝ) (P₂₁ : Matrix c a ℝ) (P₂₂ : Matrix c c ℝ) :
    let Abar : Matrix (a ⊕ r) (a ⊕ c) ℝ := zeroPad A
    Abar * (1 - fromBlocks P₁₁ P₁₂ P₂₁ P₂₂) * Abarᵀ =
      fromBlocks (A * (1 - P₁₁) * Aᵀ) 0 0 (0 : Matrix r r ℝ) := by
  dsimp [zeroPad]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, fromBlocks_transpose,
    transpose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The small residual comparison before padding and eigenvalue monotonicity. -/
theorem residual_gram_mono (A : Matrix a a ℝ) {B P : Matrix a a ℝ}
    (hBP : LoewnerLE B P) :
    LoewnerLE (A * (1 - P) * Aᵀ) (A * (1 - B) * Aᵀ) := by
  have h : LoewnerLE (1 - P) (1 - B) := by
    change ((1 - B) - (1 - P)).PosSemidef
    have heq : (1 - B) - (1 - P) = P - B := by abel
    rw [heq]
    exact hBP
  have hc := loewner_congruence h Aᵀ
  simpa only [transpose_transpose] using hc

end LowRank
