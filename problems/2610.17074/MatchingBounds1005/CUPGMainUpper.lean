import MatchingBounds1005.CUPGMachineReplay
import MatchingBounds1005.CUPGPhaseExecution
import MatchingBounds1005.CUPGEpochs

/-! The deterministic ε^(-5/3) logarithmic upper bound, using the concrete
measurable first-order machine and its exact physical oracle execution. -/
noncomputable section
namespace MatchingBounds1005.CUPG

theorem computedEpoch_calibrated {d : ℕ} {f : Model.Space d → ℝ} (hf : Differentiable ℝ f)
    (ε : ℝ) (k : ℕ) :
    computedEpoch f (rootParameter ε / 2) ((rootParameter ε) ^ 2) (rootParameter ε / 16) 4 ε
      (phaseCap (rootParameter ε) ε) k = epochPoint f ε k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [computedEpoch, ih]
    exact actualPhaseData_candidate hf _ _ _ _ _ _ _

theorem upperAlgorithm_success {d p : ℕ} {f : Model.Space d → ℝ}
    (hp : 3 ≤ p) (hf : Model.InFunctionClass p f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    () ∈ Model.Success (upperAlgorithm d ε) f ε (upperBudget ε) := by
  let r := rootParameter ε
  let N := phaseCap r ε
  let K := epochCap r
  have hK : 0 < K := by simp [K, epochCap]
  change ‖gradient f ((compileMachine (upperMachine (r / 2) (r ^ 2) (r / 16) 4 ε N)).output
    (K * phaseLength N) () (Model.transcript
      (compileMachine (upperMachine (r / 2) (r ^ 2) (r / 16) 4 ε N)) f () (K * phaseLength N)))‖ ≤ ε
  rw [compileMachine_output, upperMachine_epochs]
  change ‖gradient f (computedBest f (r / 2) (r ^ 2) (r / 16) 4 ε N K).1‖ ≤ ε
  rw [← computedBest_valid f (r / 2) (r ^ 2) (r / 16) 4 ε N K hK]
  obtain ⟨j, hj, hstationary⟩ := stationary_epoch_exists hp hf hε hεone
  have hh := computedBest_le_epoch f (r / 2) (r ^ 2) (r / 16) 4 ε N K j hj
  rw [computedEpoch_calibrated (hf.1.differentiable (by norm_num))] at hh
  exact hh.trans hstationary

end MatchingBounds1005.CUPG

namespace MatchingBounds1005.Model

theorem main_upper_bound : MainUpperBound := by
  intro p hp
  refine ⟨61920, 1, by norm_num, by norm_num, ?_⟩
  intro ε hε hεone d _hd
  refine ⟨CUPG.upperBudget ε, CUPG.upperAlgorithm d ε, CUPG.upperBudget_bound hε hεone, ?_⟩
  intro f hf
  exact CUPG.upperAlgorithm_success hp hf hε hεone

end MatchingBounds1005.Model
