import LowRank.FactorDataMeasurable

/-! Recover all visible factors (A, C, and the ambient row basis) using the
previous visible factors and one actual ambient Gram query reply. The latent
row and the right basis are not arguments to this recovery map. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

abbrev VisibleFactorData (d q r : ℕ) :=
  (Matrix (Fin q) (Fin q) ℝ × Matrix (Fin r) (Fin q) ℝ) ×
    Matrix (Fin d) (Fin q ⊕ Fin r) ℝ

def visibleFactorData {d t q r s : ℕ} (st : FactorData d t q r s) :
    VisibleFactorData d q r := (st.1, st.2.1)

theorem representedMatrix_gram {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hV : st.2.2ᵀ * st.2.2 = 1) :
    representedMatrix st D * (representedMatrix st D)ᵀ =
      st.2.1 * (fromBlocks st.1.1 0 st.1.2 D * (fromBlocks st.1.1 0 st.1.2 D)ᵀ) * st.2.1ᵀ := by
  simp only [representedMatrix, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (st.2.1 * fromBlocks st.1.1 0 st.1.2 D) st.2.2ᵀ st.2.2,
    hV, Matrix.mul_one]

theorem representedMatrix_reply_coordinates {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (z : Fin q ⊕ Fin r → ℝ)
    (hB : st.2.1ᵀ * st.2.1 = 1) (hV : st.2.2ᵀ * st.2.2 = 1) :
    st.2.1ᵀ *ᵥ ((representedMatrix st D * (representedMatrix st D)ᵀ) *ᵥ (st.2.1 *ᵥ z)) =
      (fromBlocks st.1.1 0 st.1.2 D * (fromBlocks st.1.1 0 st.1.2 D)ᵀ) *ᵥ z := by
  rw [representedMatrix_gram st D hV]
  simp only [Matrix.mulVec_mulVec]
  apply congrArg (fun M : Matrix (Fin q ⊕ Fin r) (Fin q ⊕ Fin r) ℝ => M *ᵥ z)
  calc
    _ = (st.2.1ᵀ * st.2.1) *
        (fromBlocks st.1.1 0 st.1.2 D * (fromBlocks st.1.1 0 st.1.2 D)ᵀ) *
        (st.2.1ᵀ * st.2.1) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hB, Matrix.one_mul, Matrix.mul_one]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}

def recoverVisibleFactorData (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (vis : VisibleFactorData d q (r + 1)) (reply : Fin d → ℝ) :
    VisibleFactorData d (q + 1) r :=
  let C := rotateMatrixColumns b (rowGauge b u) vis.1.2
  let w := correctedBlockReply b vis.1.2 u (vis.2ᵀ *ᵥ reply)
  ((nextExposedA vis.1.1 C (recoveredPivot w), nextExposedC C (recoveredColumn w)),
    changedBasis vis.2 (extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u))) (moveFirstTail q r))

theorem recoverVisibleFactorData_eq (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (st : FactorData d t q (r + 1) (s + 1))
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) (hst : st.Orthogonal)
    (hρ : ‖(basisCoordinates c).symm (rotateMatrixColumns b (rowGauge b u) D 0)‖ ≠ 0) :
    let X := representedMatrix st D
    let Y := rotateMatrixColumns b (rowGauge b u) D
    recoverVisibleFactorData b u (visibleFactorData st)
      ((X * Xᵀ) *ᵥ (st.2.1 *ᵥ Sum.elim 0 u)) =
      visibleFactorData (updateFactorData b c u st (revealGaussianBlock c Y).1) := by
  dsimp only
  simp only [recoverVisibleFactorData, visibleFactorData]
  rw [representedMatrix_reply_coordinates st D _ hst.1 hst.2.2.1]
  rw [recover_full_query_pivot b c _ _ _ u hu, recover_full_query_column b c _ _ _ u hu hρ]
  rfl

theorem measurable_recoverVisibleFactorData {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : S → Fin (r + 1) → ℝ) (vis : S → VisibleFactorData d q (r + 1))
    (reply : S → Fin d → ℝ) (hu : Measurable u) (hvis : Measurable vis)
    (hr : Measurable reply) :
    Measurable (fun x => recoverVisibleFactorData b (u x) (vis x) (reply x)) := by
  have hG : Measurable (fun x => gaugeMatrix b (rowGauge b (u x))) :=
    (measurable_rowGauge_matrix b).comp hu
  have hC : Measurable (fun x => rotateMatrixColumns b (rowGauge b (u x)) (vis x).1.2) := by
    simp only [rotateMatrixColumns_eq_mul]
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  have hcoord : Measurable (fun x => (vis x).2ᵀ *ᵥ reply x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  have hw := measurable_correctedBlockReply b _ _ _ hvis.fst.snd hu hcoord
  have hρ := (measurable_recoveredPivot r).comp hw
  have hc := (measurable_recoveredColumn r).comp hw
  have hL := (measurable_extendGauge (a := Fin q)).comp hG
  exact ((measurable_nextExposedA _ _ _ hvis.fst.fst hC hρ).prodMk
    (measurable_nextExposedC _ _ hC hc)).prodMk
      (measurable_changedBasis _ _ _ hvis.snd hL)

end
end LowRank
