import LowRank.VisibleOraclePolicy

/-! The updated leading row-basis column is exactly the actual query, and
previously exposed columns are retained. These identities identify the
exposed coordinate span with the queried directions. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}

theorem gaugeMatrix_query_first_row (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1) (j : Fin (r + 1)) :
    gaugeMatrix b (rowGauge b u) 0 j = u j := by
  rw [gaugeMatrix_apply, query_rotation_first_coordinate b u _ hu]
  simp [Pi.single_apply]

theorem changedBasis_query_column (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (B : Matrix (Fin d) (Fin q ⊕ Fin (r + 1)) ℝ) :
    (fun i => changedBasis B (extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u)))
      (moveFirstTail q r) i (Sum.inl 0)) = B *ᵥ Sum.elim 0 u := by
  funext i
  simp [changedBasis, moveFirstTail, extendGauge, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.transpose_apply, gaugeMatrix_query_first_row b u hu, Matrix.mulVec, dotProduct]

theorem changedBasis_old_column (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (B : Matrix (Fin d) (Fin q ⊕ Fin (r + 1)) ℝ) (j : Fin q) :
    (fun i => changedBasis B (extendGauge (a := Fin q) (gaugeMatrix b (rowGauge b u)))
      (moveFirstTail q r) i (Sum.inl j.succ)) = fun i => B i (Sum.inl j) := by
  funext i
  simp [changedBasis, moveFirstTail, extendGauge, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.transpose_apply, Matrix.one_apply]

theorem recoverVisibleFactorData_query_column (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (vis : VisibleFactorData d q (r + 1)) (reply : Fin d → ℝ) :
    (fun i => (recoverVisibleFactorData b u vis reply).2 i (Sum.inl 0)) = ambientQuery vis u :=
  changedBasis_query_column b u hu vis.2

theorem recoverVisibleFactorData_old_column (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (vis : VisibleFactorData d q (r + 1))
    (reply : Fin d → ℝ) (j : Fin q) :
    (fun i => (recoverVisibleFactorData b u vis reply).2 i (Sum.inl j.succ)) =
      fun i => vis.2 i (Sum.inl j) :=
  changedBasis_old_column b u vis.2 j

end
end LowRank
