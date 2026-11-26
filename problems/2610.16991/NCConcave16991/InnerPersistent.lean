import NCConcave16991.InnerError
import NCConcave16991.PersistentProcess

/-! # The genuine independent inner solve plugged into the persistent outer state -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

/-- The actual fresh-seed solve, using the old estimator's actual (possibly biased) error. -/
def persistentInnerSolve (P : Problem p dx dy K) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (k : ℕ) (s : PersistentProcess.State dx dy) (ω : InnerAlgorithm.Seed p.n k) : PrimalSpace dx :=
  independentInnerOutput P (selectedDualRegularization p) y0 hy0 s.center
    (PersistentProcess.error (signedComponentGradient P) y0 s) k ω

/-- In every inner step the anchor mean plus its error is exactly the stored estimate.
Thus the sampled formula uses the old estimate and two component-gradient queries. -/
theorem persistentInner_estimator_from_state (P : Problem p dx dy K) (y0 : DualSpace dy)
    (s : PersistentProcess.State dx dy) (z : JointSpace dx dy) (i : Fin p.n) :
    InnerAlgorithm.estimator (signedComponentGradient P)
      (saddleCorrection p.L (selectedDualRegularization p) y0 s.center)
      (jointPoint s.center y0) (PersistentProcess.error (signedComponentGradient P) y0 s) z i =
      s.estimate + (signedComponentGradient P i z - signedComponentGradient P i (jointPoint s.center y0)) +
        saddleCorrection p.L (selectedDualRegularization p) y0 s.center z := by
  dsimp [InnerAlgorithm.estimator, PersistentProcess.error]
  abel

/-- The anisotropic bias penalty is the actual weighted estimator energy divided by `L²`. -/
theorem innerBiasEnergy_eq_weightedErrorSq {μ : ℝ} (hμ : 0 < μ) (ξ : JointSpace dx dy) :
    innerBiasEnergy p μ ξ = weightedErrorSq (p.L / μ) ξ / p.L ^ 2 := by
  dsimp [innerBiasEnergy, weightedErrorSq]
  field_simp [p.L_pos.ne', hμ.ne'] <;> ring

/-- This discharges the persistent process's inner-solve interface for every actual state. -/
theorem persistentInnerSolve_error (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) {k : ℕ}
    (hk : 4294967296 * (p.L / selectedDualRegularization p) ^ 2 ≤ (k : ℝ))
    (s : PersistentProcess.State dx dy) :
    (∫ ω, ‖persistentInnerSolve P y0 hy0 k s ω -
      proximalMap p.L_pos (dualRegularizedValue_continuous P hAS (selectedDualRegularization p) y0)
        (dualRegularizedValue_bddBelow P (selectedDualRegularization_pos p).le y0 hy0) s.center‖ ^ 2
      ∂InnerAlgorithm.seedLaw k) ≤
      (1 / 1024 : ℝ) *
        ‖proximalMap p.L_pos (dualRegularizedValue_continuous P hAS (selectedDualRegularization p) y0)
          (dualRegularizedValue_bddBelow P (selectedDualRegularization_pos p).le y0 hy0) s.center - s.center‖ ^ 2 +
        (3 / p.L ^ 2) * weightedErrorSq (p.L / selectedDualRegularization p)
          (PersistentProcess.error (signedComponentGradient P) y0 s) +
        p.epsilon ^ 2 / (4294967296 * p.L ^ 2) := by
  have h := independentInner_selected_error P hAS y0 hy0 s.center
    (PersistentProcess.error (signedComponentGradient P) y0 s) hk
  rw [innerBiasEnergy_eq_weightedErrorSq (selectedDualRegularization_pos p)] at h
  change (∫ ω, ‖persistentInnerSolve P y0 hy0 k s ω -
      proximalMap p.L_pos (dualRegularizedValue_continuous P hAS (selectedDualRegularization p) y0)
        (dualRegularizedValue_bddBelow P (selectedDualRegularization_pos p).le y0 hy0) s.center‖ ^ 2
      ∂InnerAlgorithm.seedLaw k) ≤ _ at h
  convert h using 1 <;> ring

end NCConcave16991
