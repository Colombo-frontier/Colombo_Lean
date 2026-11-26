import Matvec.TwoSidedPosteriorCentered
import Matvec.BlockGaussianLow

/-! Completing the actual residual frames to orthogonal coordinates and
identifying the visible/hidden block decomposition. -/
namespace Matvec
open Matrix MeasureTheory LowRank
open scoped Matrix
noncomputable section

def finiteEuclideanMap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

theorem finiteEuclideanMap_norm_of_orthonormal_columns {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) (hA : Aᵀ * A = 1)
    (x : EuclideanSpace ℝ κ) : ‖finiteEuclideanMap A x‖ = ‖x‖ := by
  exact toEuclideanLin_norm_of_orthonormal_columns A hA x

def posteriorComplement {k q : ℕ} (U : Matrix (Fin (k + q)) (Fin k) ℝ) :=
  kernelFrame Uᵀ q

def posteriorFullFrame {k q : ℕ} (U : Matrix (Fin (k + q)) (Fin k) ℝ) :
    Matrix (Fin (k + q)) (Fin q ⊕ Fin k) ℝ :=
  Matrix.fromCols (posteriorComplement U) U

theorem posteriorComplement_orthogonal {k q : ℕ}
    (U : Matrix (Fin (k + q)) (Fin k) ℝ) :
    (posteriorComplement U)ᵀ * posteriorComplement U = 1 :=
  kernelFrame_orthonormal _ le_rfl

theorem posteriorComplement_annihilates {k q : ℕ}
    (U : Matrix (Fin (k + q)) (Fin k) ℝ) : Uᵀ * posteriorComplement U = 0 :=
  mul_kernelFrame Uᵀ q

theorem posteriorFullFrame_orthogonal {k q : ℕ}
    (U : Matrix (Fin (k + q)) (Fin k) ℝ) (hU : Uᵀ * U = 1) :
    (posteriorFullFrame U)ᵀ * posteriorFullFrame U = 1 := by
  have hcross : (posteriorComplement U)ᵀ * U = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose (posteriorComplement_annihilates U)
  rw [posteriorFullFrame, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    posteriorComplement_orthogonal, posteriorComplement_annihilates, hcross, hU]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem posteriorFullFrame_complete {k q : ℕ}
    (U : Matrix (Fin (k + q)) (Fin k) ℝ) (hU : Uᵀ * U = 1) :
    posteriorFullFrame U * (posteriorFullFrame U)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv
    ((finSumFinEquiv : Fin q ⊕ Fin k ≃ Fin (q + k)).trans
      (finCongr (Nat.add_comm q k)))).mp (posteriorFullFrame_orthogonal U hU)

theorem fullCoordinates_leastStretch {m q k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (P Q : Matrix (Fin m) (Fin q ⊕ Fin k) ℝ)
    (hP : Pᵀ * P = 1) (hPc : P * Pᵀ = 1) (hQ : Qᵀ * Q = 1) :
    leastStretch (matrixEuclideanMap M) ≤ leastStretch (finiteEuclideanMap (Pᵀ * M * Q)) := by
  have hunit : ∃ x : EuclideanSpace ℝ (Fin q ⊕ Fin k), ‖x‖ = 1 :=
    ⟨(EuclideanSpace.basisFun _ ℝ) (Sum.inr ⟨0, hk⟩),
      (EuclideanSpace.basisFun _ ℝ).norm_eq_one _⟩
  apply leastStretch_le_of_lifts _ _ hunit
  intro z hz
  refine ⟨finiteEuclideanMap Q z, ?_, ?_⟩
  · rw [finiteEuclideanMap_norm_of_orthonormal_columns Q hQ, hz]
  · have hm : matrixEuclideanMap M (finiteEuclideanMap Q z) =
        finiteEuclideanMap P (finiteEuclideanMap (Pᵀ * M * Q) z) := by
      apply (WithLp.equiv 2 (Fin m → ℝ)).injective
      change M *ᵥ (Q *ᵥ (z : _ → ℝ)) = P *ᵥ ((Pᵀ * M * Q) *ᵥ (z : _ → ℝ))
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPc, Matrix.one_mul]
    rw [hm, finiteEuclideanMap_norm_of_orthonormal_columns P hP]

def posteriorVisibleBlocks {k q : ℕ} (st : TwoSidedState (k + q) (k + q) k k) :=
  ((posteriorComplement st.2.1)ᵀ * st.1 * posteriorComplement st.2.2,
    ((posteriorComplement st.2.1)ᵀ * st.1 * st.2.2,
      st.2.1ᵀ * st.1 * posteriorComplement st.2.2))

theorem posteriorFullFrame_blocks {k q : ℕ}
    (st : TwoSidedState (k + q) (k + q) k k) (ho : st.Orthogonal) (hc : st.Centered)
    (D : Matrix (Fin k) (Fin k) ℝ) :
    (posteriorFullFrame st.2.1)ᵀ * representedTwoSided st D * posteriorFullFrame st.2.2 =
      Matrix.fromBlocks (posteriorVisibleBlocks st).1 (posteriorVisibleBlocks st).2.1
        (posteriorVisibleBlocks st).2.2 D := by
  have hleft0 : (posteriorComplement st.2.1)ᵀ * st.2.1 = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose (posteriorComplement_annihilates st.2.1)
  have hl : (posteriorComplement st.2.1)ᵀ * representedTwoSided st D =
      (posteriorComplement st.2.1)ᵀ * st.1 := by
    unfold representedTwoSided
    rw [Matrix.mul_add]
    simp only [← Matrix.mul_assoc, hleft0, Matrix.zero_mul, add_zero]
  have hr : representedTwoSided st D * posteriorComplement st.2.2 =
      st.1 * posteriorComplement st.2.2 := by
    unfold representedTwoSided
    rw [Matrix.add_mul]
    simp only [Matrix.mul_assoc, posteriorComplement_annihilates, Matrix.mul_zero, add_zero]
  simp only [posteriorFullFrame, Matrix.transpose_fromCols]
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hl]
  rw [representedTwoSided_hidden_block st ho hc,
    Matrix.mul_assoc st.2.1ᵀ (representedTwoSided st D) (posteriorComplement st.2.2), hr]
  simp only [posteriorVisibleBlocks, Matrix.mul_assoc]

theorem representedTwoSided_leastStretch_block {k q : ℕ} (hk : 0 < k)
    (st : TwoSidedState (k + q) (k + q) k k) (ho : st.Orthogonal) (hc : st.Centered)
    (D : Matrix (Fin k) (Fin k) ℝ) :
    leastStretch (matrixEuclideanMap (representedTwoSided st D)) ≤
      leastStretch (blockEuclideanMap (posteriorVisibleBlocks st).1
        (posteriorVisibleBlocks st).2.1 (posteriorVisibleBlocks st).2.2 D) := by
  have h := fullCoordinates_leastStretch hk (representedTwoSided st D)
    (posteriorFullFrame st.2.1) (posteriorFullFrame st.2.2)
    (posteriorFullFrame_orthogonal st.2.1 ho.1) (posteriorFullFrame_complete st.2.1 ho.1)
    (posteriorFullFrame_orthogonal st.2.2 ho.2)
  rw [posteriorFullFrame_blocks st ho hc] at h
  exact h

/-- Uniform pointwise low event for the actual centered affine posterior,
with no assumed Gaussian-core or Schur comparison hypothesis. -/
theorem representedTwoSided_gaussian_low (q n : ℕ) (hn : lowEventRank ≤ n)
    (st : TwoSidedState ((q + (n + 1)) + q) ((q + (n + 1)) + q)
      (q + (n + 1)) (q + (n + 1))) (ho : st.Orthogonal) (hc : st.Centered)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {D | leastStretch (matrixEuclideanMap (representedTwoSided st D)) ≤
          2 * a / Real.sqrt (n + 1 : ℝ)} := by
  apply (block_gaussian_leastStretch_low q n hn (posteriorVisibleBlocks st).1
    (posteriorVisibleBlocks st).2.1 (posteriorVisibleBlocks st).2.2 ha ha1).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro D hD
  exact (representedTwoSided_leastStretch_block (by omega) st ho hc D).trans hD

end
end Matvec
