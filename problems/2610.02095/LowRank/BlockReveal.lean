import LowRank.BlockKernel
import LowRank.GaussianAdaptiveReply

/-! One full block update. The newly queried row and newly exposed column
are placed first among the exposed coordinates. Reversing exposure order
avoids arbitrary index casts and preserves a triangular exposed block. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def moveFirstTail (q r : ℕ) : (Fin (q + 1) ⊕ Fin r) ≃ (Fin q ⊕ Fin (r + 1)) where
  toFun := Sum.elim (Fin.cases (Sum.inr 0) (fun i => Sum.inl i)) (fun i => Sum.inr i.succ)
  invFun := Sum.elim (fun i => Sum.inl i.succ) (Fin.cases (Sum.inl 0) (fun i => Sum.inr i))
  left_inv := by
    intro i
    cases i with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr i => rfl
  right_inv := by
    intro i
    cases i with
    | inl i => rfl
    | inr i => exact Fin.cases rfl (fun _ => rfl) i

def nextExposedA {q r : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin (r + 1)) (Fin q) ℝ) (ρ : ℝ) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  Fin.cons (Fin.cons ρ (C 0)) (fun i => Fin.cons 0 (A i))

def nextExposedC {q r : ℕ} (C : Matrix (Fin (r + 1)) (Fin q) ℝ) (c : Fin r → ℝ) :
    Matrix (Fin r) (Fin (q + 1)) ℝ := fun i => Fin.cons (c i) (C i.succ)

theorem block_query_reply {q r s : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin r) (Fin q) ℝ) (D : Matrix (Fin r) (Fin s) ℝ) (u : Fin r → ℝ) :
    let X := fromBlocks A 0 C D
    (X * Xᵀ) *ᵥ Sum.elim 0 u =
      Sum.elim (A *ᵥ (Cᵀ *ᵥ u)) ((C * Cᵀ) *ᵥ u + (D * Dᵀ) *ᵥ u) := by
  dsimp only
  rw [exposed_gram_blocks, fromBlocks_mulVec]
  simp [Matrix.mulVec_mulVec, Matrix.add_mulVec]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

theorem revealed_full_block_update {q r s : ℕ}
    (b : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin (r + 1)) (Fin q) ℝ)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    (fromBlocks A 0 C (rotateMatrixRows b (rowGauge b (D 0)) D)).submatrix
      (moveFirstTail q r) (moveFirstTail q s) =
    fromBlocks (nextExposedA A C ‖(basisCoordinates b).symm (D 0)‖) 0
      (nextExposedC C (revealGaussianBlock b D).1.2) (revealGaussianBlock b D).2 := by
  ext i j
  cases i with
  | inl i =>
    refine Fin.cases ?_ (fun i => ?_) i
    · cases j with
      | inl j =>
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa [submatrix, moveFirstTail, rotateMatrixRows, nextExposedA] using rowGauge_aligns b (D 0) 0
        · rfl
      | inr j =>
        simpa [submatrix, moveFirstTail, rotateMatrixRows] using rowGauge_aligns b (D 0) j.succ
    · cases j with
      | inl j => exact Fin.cases rfl (fun _ => rfl) j
      | inr j => rfl
  | inr i =>
    cases j with
    | inl j => exact Fin.cases rfl (fun _ => rfl) j
    | inr j => rfl

theorem nextExposedA_injective {q r : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin (r + 1)) (Fin q) ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hA : Function.Injective (Matrix.mulVec A)) :
    Function.Injective (Matrix.mulVec (nextExposedA A C ρ)) := by
  suffices hker : ∀ z, nextExposedA A C ρ *ᵥ z = 0 → z = 0 by
    intro z w hzw
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hzw, sub_self]
  intro z hz
  have htail : A *ᵥ (fun j => z j.succ) = 0 := by
    funext i
    have hi := congrFun hz i.succ
    simpa [nextExposedA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hi
  have htailzero : (fun j : Fin q => z j.succ) = 0 := hA (by simpa using htail)
  have hfirst := congrFun hz 0
  have hzero : z 0 = 0 := by
    have hmul : ρ * z 0 = 0 := by
      simpa [nextExposedA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        show ∀ j : Fin q, z j.succ = 0 from fun j => congrFun htailzero j] using hfirst
    exact (mul_eq_zero.mp hmul).resolve_left hρ
  funext i
  exact Fin.cases hzero (fun j => congrFun htailzero j) i

end
end LowRank
