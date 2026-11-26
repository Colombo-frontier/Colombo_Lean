import LowRank.AmbientStepSimulation
import LowRank.OracleProcessSimulation

/-! Decode the entire original arbitrary-query history from the normalized
Gaussian execution. Every step preserves both the original memory and the
agreement between the visible replay and complete factor state. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

theorem reduceAmbientOracle_gaussian_simulates (d t r s n q : ℕ) {S T U : Type u}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (policy : AmbientOraclePolicy d n S) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + n)))
    (st : MeasurableStateMap U (FactorData d t q (r + n) (s + n))) (nm : MeasurableStateMap U T)
    (p : U × Matrix (Fin (r + n)) (Fin (s + n)) ℝ)
    (hvis : vis.1 (nm.1 p.1) = visibleFactorData (st.1 p.1)) (hst : (st.1 p.1).Orthogonal)
    (hreg : GaussianPolicy.Regular r s n (compileVisibleOracle d t r s n q
      (reduceAmbientOracle d r n q policy mem vis) st nm) p) :
    let vp := reduceAmbientOracle d r n q policy mem vis
    let gp := compileVisibleOracle d t r s n q vp st nm
    let X := representedMatrix (st.1 p.1) p.2
    runAmbientOracle d n policy (X * Xᵀ) (mem.1 (nm.1 p.1)) =
      readReducedHistory d r n q policy mem vis
        (readOracleHistory d t r s n q vp st nm (runGaussianPolicy r s n gp p).1) := by
  induction n generalizing q S T U with
  | zero => rfl
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let uq := liftVisibleQuery (ambientPolicyDirection b policy.1 mem vis) st nm
    let st' := advanceFactorState b c uq st
    let nm' := advanceOracleMemory b c uq st nm
    let mem' := advanceReducedMemory b policy.1 mem vis
    let vis' := advanceReducedVisible b policy.1 mem vis
    let vp' := reduceAmbientOracle d r n (q + 1) policy.2 mem' vis'
    let gp' := compileVisibleOracle d t r s n (q + 1) vp' st' nm'
    let step := adaptiveGaussianStep b c uq.1 p
    change 0 < ‖(basisCoordinates c).symm step.1.2.1‖ ∧
      GaussianPolicy.Regular r s n gp' step at hreg
    have hstep := ambientStep_simulation b c policy.1 mem vis st nm p hvis hst (ne_of_gt hreg.1)
    have hmem : mem'.1 (nm'.1 step.1) =
        (mem.1 (nm.1 p.1), (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ) *ᵥ
          policy.1.1 (mem.1 (nm.1 p.1))) := hstep.1
    have hmatch : vis'.1 (nm'.1 step.1) = visibleFactorData (st'.1 step.1) := hstep.2
    have horth : (st'.1 step.1).Orthogonal := updateFactorData_orthogonal b c _ _ _ hst
    have hrec : representedMatrix (st'.1 step.1) step.2 = representedMatrix (st.1 p.1) p.2 :=
      updateFactorData_preserves_matrix b c _ _ _
    have h := ih (q + 1) policy.2 mem' vis' st' nm' step hmatch horth hreg.2
    dsimp only at h
    rw [hrec, hmem] at h
    exact h

end
end LowRank
