import LowRank.OracleGaussianCompile

/-! One actual oracle step agrees with the compiled Gaussian step, including
the stored reply and every new visible factor. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem visibleOracleStep_simulation {S T E F : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : MeasurableStateMap (T × VisibleFactorData d q (r + 1)) (Fin (r + 1) → ℝ))
    (st : MeasurableStateMap S (FactorData d t q (r + 1) (s + 1)))
    (mem : MeasurableStateMap S T) (p : S × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hu : ‖(basisCoordinates b).symm ((liftVisibleQuery u st mem).1 p.1)‖ = 1)
    (hst : (st.1 p.1).Orthogonal)
    (hρ : ‖(basisCoordinates c).symm
      (rotateMatrixColumns b (rowGauge b ((liftVisibleQuery u st mem).1 p.1)) p.2 0)‖ ≠ 0) :
    let uq := liftVisibleQuery u st mem
    let step := adaptiveGaussianStep b c uq.1 p
    let X := representedMatrix (st.1 p.1) p.2
    visibleOracleStep b u.1 (X * Xᵀ) (mem.1 p.1, visibleFactorData (st.1 p.1)) =
      ((advanceOracleMemory b c uq st mem).1 step.1,
        visibleFactorData ((advanceFactorState b c uq st).1 step.1)) := by
  have hr := decodeFactorReply_eq b c ((liftVisibleQuery u st mem).1 p.1) (st.1 p.1) p.2 hu hst
  have hv := recoverVisibleFactorData_eq b c ((liftVisibleQuery u st mem).1 p.1)
    (st.1 p.1) p.2 hu hst hρ
  exact Prod.ext (Prod.ext rfl hr.symm) hv

end
end LowRank
