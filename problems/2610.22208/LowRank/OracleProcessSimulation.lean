import LowRank.OracleStepSimulation
import LowRank.GaussianRegularProcess

/-! A complete finite actual oracle transcript and all visible factors agree
with the compiled Gaussian process on the full-measure regular-pivot event. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

theorem compileVisibleOracle_simulates (d t r s n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : VisibleOraclePolicy d r n q T)
    (st : MeasurableStateMap S (FactorData d t q (r + n) (s + n))) (mem : MeasurableStateMap S T)
    (hunit : VisibleOraclePolicy.IsUnit d r n q policy)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) (hst : (st.1 p.1).Orthogonal)
    (hreg : GaussianPolicy.Regular r s n (compileVisibleOracle d t r s n q policy st mem) p) :
    let gp := compileVisibleOracle d t r s n q policy st mem
    let out := runGaussianPolicy r s n gp p
    let X := representedMatrix (st.1 p.1) p.2
    runVisibleOracle d r n q policy (X * Xᵀ) (mem.1 p.1, visibleFactorData (st.1 p.1)) =
      (readOracleHistory d t r s n q policy st mem out.1,
        visibleFactorData (finalFactorData d t r s n q gp st.1 out.1)) := by
  induction n generalizing q S T with
  | zero => rfl
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let uq := liftVisibleQuery policy.1 st mem
    let st' := advanceFactorState b c uq st
    let mem' := advanceOracleMemory b c uq st mem
    let gp' := compileVisibleOracle d t r s n (q + 1) policy.2 st' mem'
    let step := adaptiveGaussianStep b c uq.1 p
    have hu : ‖(basisCoordinates b).symm (uq.1 p.1)‖ = 1 :=
      hunit.1 (mem.1 p.1, visibleFactorData (st.1 p.1))
    change 0 < ‖(basisCoordinates c).symm step.1.2.1‖ ∧
      GaussianPolicy.Regular r s n gp' step at hreg
    have heq := visibleOracleStep_simulation b c policy.1 st mem p hu hst (ne_of_gt hreg.1)
    have horth : (st'.1 step.1).Orthogonal :=
      updateFactorData_orthogonal b c _ _ _ hst
    have hrec : representedMatrix (st'.1 step.1) step.2 = representedMatrix (st.1 p.1) p.2 :=
      updateFactorData_preserves_matrix b c _ _ _
    change runVisibleOracle d r n (q + 1) policy.2
      (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ)
      (visibleOracleStep b policy.1.1
        (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ)
        (mem.1 p.1, visibleFactorData (st.1 p.1))) =
      (readOracleHistory d t r s n (q + 1) policy.2 st' mem'
          (runGaussianPolicy r s n gp' step).1,
        visibleFactorData (finalFactorData d t r s n (q + 1) gp' st'.1
          (runGaussianPolicy r s n gp' step).1))
    rw [heq]
    have h := ih (q + 1) policy.2 st' mem' hunit.2 step horth hreg.2
    dsimp only at h
    rw [hrec] at h
    exact h

theorem compileVisibleOracle_simulates_ae (d t r s n q : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (ν : Measure S) [SFinite ν]
    (policy : VisibleOraclePolicy d r n q T)
    (st : MeasurableStateMap S (FactorData d t q (r + n) (s + n))) (mem : MeasurableStateMap S T)
    (hunit : VisibleOraclePolicy.IsUnit d r n q policy)
    (hst : ∀ᵐ x ∂ν, (st.1 x).Orthogonal) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      let gp := compileVisibleOracle d t r s n q policy st mem
      let out := runGaussianPolicy r s n gp p
      let X := representedMatrix (st.1 p.1) p.2
      runVisibleOracle d r n q policy (X * Xᵀ) (mem.1 p.1, visibleFactorData (st.1 p.1)) =
        (readOracleHistory d t r s n q policy st mem out.1,
          visibleFactorData (finalFactorData d t r s n q gp st.1 out.1)) := by
  have ho : ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v), (st.1 p.1).Orthogonal :=
    Measure.quasiMeasurePreserving_fst.ae hst
  filter_upwards [ho, gaussianPolicy_regular_ae r s n ν
    (compileVisibleOracle d t r s n q policy st mem) hv] with p hp hreg
  exact compileVisibleOracle_simulates d t r s n q policy st mem hunit p hp hreg

end
end LowRank
