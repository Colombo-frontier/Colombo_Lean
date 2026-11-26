import LowRank.MatrixOrder
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Rank

/-! Algebraic content of the Gaussian factorization and the nullspace graph.
These results hold for deterministic matrices. Independence, Gaussianity and
measurable choice of the factorization are separate obligations. -/

namespace LowRank
open Matrix
open scoped Matrix

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

theorem gram_kernel_iff (X : Matrix a b ℝ) (v : a → ℝ) :
    (X * Xᵀ) *ᵥ v = 0 ↔ Xᵀ *ᵥ v = 0 := by
  have h := Matrix.ker_mulVecLin_transpose_mul_self Xᵀ
  have hm := SetLike.ext_iff.mp h v
  simpa only [LinearMap.mem_ker, mulVecLin_apply, transpose_transpose] using hm

theorem block_transpose_kernel_iff
    (A : Matrix a a ℝ) (C : Matrix b a ℝ) (D : Matrix b c ℝ)
    (x : a → ℝ) (y : b → ℝ) :
    (fromBlocks A 0 C D)ᵀ *ᵥ Sum.elim x y = 0 ↔
      Aᵀ *ᵥ x + Cᵀ *ᵥ y = 0 ∧ Dᵀ *ᵥ y = 0 := by
  rw [fromBlocks_transpose, fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, transpose_zero,
    zero_mulVec, zero_add]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨h₁, h₂⟩
    funext i
    cases i <;> simp [h₁, h₂]

/-- Graph formula without any inversion convention: `B` solves `Aᵀ B = Cᵀ`. -/
theorem block_kernel_graph_iff
    (A : Matrix a a ℝ) (C : Matrix b a ℝ) (D : Matrix b c ℝ)
    (B : Matrix a b ℝ)
    (hA : Function.Injective (fun x => Aᵀ *ᵥ x)) (hB : Aᵀ * B = Cᵀ)
    (x : a → ℝ) (y : b → ℝ) :
    (fromBlocks A 0 C D)ᵀ *ᵥ Sum.elim x y = 0 ↔
      x = -(B *ᵥ y) ∧ Dᵀ *ᵥ y = 0 := by
  rw [block_transpose_kernel_iff]
  have hzero : Aᵀ *ᵥ x + Cᵀ *ᵥ y = 0 ↔ x = -(B *ᵥ y) := by
    constructor
    · intro h
      apply hA
      dsimp only
      rw [mulVec_neg, mulVec_mulVec, hB]
      exact eq_neg_of_add_eq_zero_left h
    · intro h
      rw [h, mulVec_neg, mulVec_mulVec, hB, neg_add_cancel]
  exact and_congr_left (fun _ => hzero)

/-- The graph identity for the actual Gram matrix `W = X Xᵀ`. -/
theorem gram_block_kernel_graph_iff
    (A : Matrix a a ℝ) (C : Matrix b a ℝ) (D : Matrix b c ℝ)
    (B : Matrix a b ℝ)
    (hA : Function.Injective (fun x => Aᵀ *ᵥ x)) (hB : Aᵀ * B = Cᵀ)
    (x : a → ℝ) (y : b → ℝ) :
    let X := fromBlocks A 0 C D
    (X * Xᵀ) *ᵥ Sum.elim x y = 0 ↔
      x = -(B *ᵥ y) ∧ Dᵀ *ᵥ y = 0 := by
  dsimp
  rw [gram_kernel_iff]
  exact block_kernel_graph_iff A C D B hA hB x y

theorem exposed_gram_blocks (A : Matrix a a ℝ) (C : Matrix b a ℝ)
    (D : Matrix b c ℝ) :
    let X := fromBlocks A 0 C D
    X * Xᵀ = fromBlocks (A * Aᵀ) (A * Cᵀ) (C * Aᵀ) (C * Cᵀ + D * Dᵀ) := by
  dsimp
  rw [fromBlocks_transpose, fromBlocks_multiply]
  simp

/-- The quotient map used for exact range recovery, evaluated on a factor vector. -/
theorem quotient_factor_action (A : Matrix a a ℝ) (C : Matrix b a ℝ)
    (D : Matrix b c ℝ) (R : Matrix a a ℝ) (hR : R * A = 1)
    (u : a → ℝ) (v : c → ℝ) :
    (C *ᵥ u + D *ᵥ v) - C *ᵥ (R *ᵥ (A *ᵥ u)) = D *ᵥ v := by
  have hRu : R *ᵥ (A *ᵥ u) = u := by
    rw [mulVec_mulVec, hR, one_mulVec]
  rw [hRu]
  abel

end LowRank
