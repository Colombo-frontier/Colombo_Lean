import LowRank.ExposedRecovery

/-! Subtracting the known exposed-block contribution from a full Gram query
recovers precisely the hidden-block reply used by the Gaussian revelation.
All recovery formulas are measurable in known blocks, query, and reply. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {q r s : ℕ}

def correctedBlockReply (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (C : Matrix (Fin (r + 1)) (Fin q) ℝ) (u : Fin (r + 1) → ℝ)
    (w : Fin q ⊕ Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  coordinateRotation b (rowGauge b u) ((fun i => w (Sum.inr i)) - (C * Cᵀ) *ᵥ u)

theorem correctedBlockReply_eq (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin (r + 1)) (Fin q) ℝ)
    (D : Matrix (Fin (r + 1)) (Fin s) ℝ) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) :
    let X := fromBlocks A 0 C D
    let Y := rotateMatrixColumns b (rowGauge b u) D
    correctedBlockReply b C u ((X * Xᵀ) *ᵥ Sum.elim 0 u) = fun i => (Y * Yᵀ) i 0 := by
  dsimp only
  rw [correctedBlockReply, block_query_reply]
  simp only [Sum.elim_inr]
  rw [add_sub_cancel_left]
  exact (query_rotation_gram_reply b u hu D).symm

theorem measurable_correctedBlockReply {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (C : S → Matrix (Fin (r + 1)) (Fin q) ℝ) (u : S → Fin (r + 1) → ℝ)
    (w : S → Fin q ⊕ Fin (r + 1) → ℝ) (hC : Measurable C) (hu : Measurable u)
    (hw : Measurable w) : Measurable (fun st => correctedBlockReply b (C st) (u st) (w st)) := by
  have hm : Measurable (fun st => (fun i => w st (Sum.inr i)) - (C st * (C st)ᵀ) *ᵥ u st) := by
    apply measurable_pi_lambda
    intro i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have harg := hu.prodMk hm
  simpa only [Function.comp_def, correctedBlockReply] using
    (measurable_coordinate_rowGauge b).comp harg

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

theorem recover_full_query_pivot (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin (r + 1)) (Fin q) ℝ)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) :
    let X := fromBlocks A 0 C D
    let Y := rotateMatrixColumns b (rowGauge b u) D
    recoveredPivot (correctedBlockReply b C u ((X * Xᵀ) *ᵥ Sum.elim 0 u)) =
      ‖(basisCoordinates c).symm (Y 0)‖ := by
  dsimp only
  rw [correctedBlockReply_eq b A C D u hu, recoveredPivot_gram c]

theorem recover_full_query_column (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin (r + 1)) (Fin q) ℝ)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (hρ : ‖(basisCoordinates c).symm (rotateMatrixColumns b (rowGauge b u) D 0)‖ ≠ 0) :
    let X := fromBlocks A 0 C D
    let Y := rotateMatrixColumns b (rowGauge b u) D
    recoveredColumn (correctedBlockReply b C u ((X * Xᵀ) *ᵥ Sum.elim 0 u)) =
      (revealGaussianBlock c Y).1.2 := by
  dsimp only
  rw [correctedBlockReply_eq b A C D u hu, recoveredColumn_gram c _ hρ]

end
end LowRank
