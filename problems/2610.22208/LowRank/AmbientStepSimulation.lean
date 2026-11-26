import LowRank.AmbientPolicyCompile
import LowRank.OracleStepSimulation

/-! The arbitrary-query decoder and visible-state replay agree with one
actual Gaussian revelation step, including the zero-residual case. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem ambientStep_simulation {S T U E F : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (v : MeasurableStateMap S (Fin d → ℝ)) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + 1)))
    (st : MeasurableStateMap U (FactorData d t q (r + 1) (s + 1))) (nm : MeasurableStateMap U T)
    (p : U × Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hvis : vis.1 (nm.1 p.1) = visibleFactorData (st.1 p.1)) (hst : (st.1 p.1).Orthogonal)
    (hρ : ‖(basisCoordinates c).symm
      (rotateMatrixColumns b (rowGauge b ((liftVisibleQuery (ambientPolicyDirection b v mem vis) st nm).1 p.1))
        p.2 0)‖ ≠ 0) :
    let uq := liftVisibleQuery (ambientPolicyDirection b v mem vis) st nm
    let step := adaptiveGaussianStep b c uq.1 p
    let nm' := advanceOracleMemory b c uq st nm
    let X := representedMatrix (st.1 p.1) p.2
    (advanceReducedMemory b v mem vis).1 (nm'.1 step.1) =
        (mem.1 (nm.1 p.1), (X * Xᵀ) *ᵥ v.1 (mem.1 (nm.1 p.1))) ∧
      (advanceReducedVisible b v mem vis).1 (nm'.1 step.1) =
        visibleFactorData ((advanceFactorState b c uq st).1 step.1) := by
  let uq := liftVisibleQuery (ambientPolicyDirection b v mem vis) st nm
  have hu : ‖(basisCoordinates b).symm (uq.1 p.1)‖ = 1 := reducedQueryDirection_norm b _ _
  have hq : uq.1 p.1 = reducedQueryDirection b (visibleFactorData (st.1 p.1))
      (v.1 (mem.1 (nm.1 p.1))) := by
    change reducedQueryDirection b (vis.1 (nm.1 p.1)) _ = _
    rw [hvis]
  have hr := decodeFactorReply_eq b c (uq.1 p.1) (st.1 p.1) p.2 hu hst
  constructor
  · apply Prod.ext
    · rfl
    change decodeReducedQuery b (vis.1 (nm.1 p.1)) (v.1 (mem.1 (nm.1 p.1)))
      (decodeFactorReply b c (uq.1 p.1) (visibleFactorData (st.1 p.1))
        (revealGaussianBlock c (rotateMatrixColumns b (rowGauge b (uq.1 p.1)) p.2)).1) = _
    rw [hvis, hr, hq]
    exact decodeReducedQuery_eq b (st.1 p.1) p.2 hst _
  · change recoverVisibleFactorData b
      (reducedQueryDirection b (vis.1 (nm.1 p.1)) (v.1 (mem.1 (nm.1 p.1)))) (vis.1 (nm.1 p.1))
      (decodeFactorReply b c (uq.1 p.1) (visibleFactorData (st.1 p.1))
        (revealGaussianBlock c (rotateMatrixColumns b (rowGauge b (uq.1 p.1)) p.2)).1) = _
    rw [hvis, ← hq, hr]
    exact recoverVisibleFactorData_eq b c (uq.1 p.1) (st.1 p.1) p.2 hu hst hρ

end
end LowRank
