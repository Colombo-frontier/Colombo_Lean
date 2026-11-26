import RandomizedFO2003.MachineRunSimulation
import RandomizedFO2003.UpperRate

namespace RandomizedFO2003.Accelerated

open MeasureTheory

noncomputable section

def acceleratedAlgorithm (d : ℕ) (ε L ρ : ℝ) : Model.Algorithm d Unit :=
  let η := stepSize L
  let B := accuracyRadius ε ρ
  (acceleratedMachine η (roundedMomentum η ρ B) B (epochHorizon η ρ B) (0 : Model.Space d)).algorithm

def acceleratedBudget (ε Δ L ρ : ℝ) : ℕ :=
  restartLimit Δ (ρ * accuracyRadius ε ρ ^ 3) * epochHorizon (stepSize L) ρ (accuracyRadius ε ρ)

variable {ε Δ L ρ : ℝ}
local notation "η₀" => stepSize L
local notation "B₀" => accuracyRadius ε ρ
local notation "N₀" => epochHorizon η₀ ρ B₀
local notation "θ₀" => roundedMomentum η₀ ρ B₀

theorem accuracy_epochOutput {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (start : E) (hbudget : (N₀ : ℝ) * epochEnergy f η₀ θ₀ start N₀ ≤ B₀ ^ 2) :
    ‖gradient f (epochOutput f η₀ θ₀ N₀ start)‖ ≤ ε := by
  have hp := roundedMomentum_conditions (stepSize_pos hL) hρ (accuracyRadius_pos hε hρ)
    (accuracy_rawMomentum_small hε hL hρ haccuracy)
  have hq := halfMinIndex_spec (fun n => ‖epochIncrement f η₀ θ₀ start n‖) hp.1
  exact accuracy_epoch_terminal start hf hε hL hρ haccuracy hH hq.1 hq.2.1 hq.2.2 hbudget

/-- Correctness for the original function class and actual full-history
first-order algorithm, at the exact integer oracle-call budget. -/
theorem accelerated_algorithm_correct {d : ℕ}
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (f : Model.Space d → ℝ) (hf : Model.InFunctionClass f Δ L ρ) :
    ‖gradient f ((acceleratedAlgorithm d ε L ρ).output (acceleratedBudget ε Δ L ρ) ()
      (Model.transcript (acceleratedAlgorithm d ε L ρ) f () (acceleratedBudget ε Δ L ρ)))‖ ≤ ε := by
  have hp := roundedMomentum_conditions (stepSize_pos hL) hρ (accuracyRadius_pos hε hρ)
    (accuracy_rawMomentum_small hε hL hρ haccuracy)
  change ‖gradient f ((acceleratedMachine η₀ θ₀ B₀ N₀ (0 : Model.Space d)).algorithm.output
    (restartLimit Δ (ρ * B₀ ^ 3) * N₀) ()
    (Model.transcript (acceleratedMachine η₀ θ₀ B₀ N₀ (0 : Model.Space d)).algorithm f ()
      (restartLimit Δ (ρ * B₀ ^ 3) * N₀)))‖ ≤ ε
  rw [accelerated_output_transcript f η₀ θ₀ B₀ N₀ 0 hp.1]
  apply blockOutputSequence_accurate_of_success f η₀ θ₀ B₀ ε N₀ 0
    (accuracy_epochOutput hf.1 hε hL hρ haccuracy hf.2.2.2)
  exact exists_successful_epoch hf.1 hε hL hρ haccuracy hf.2.2.1 hf.2.2.2 0 hf.2.1

theorem accelerated_budget_le_rate (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ)
    (hmass : 1 ≤ Δ * ρ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) :
    (acceleratedBudget ε Δ L ρ : ℝ) ≤ (512 : ℝ) ^ (7 / 4 : ℝ) * Model.rate ε Δ L ρ :=
  configured_query_cost_le hε hL hρ hmass

theorem accelerated_success_eq_univ {d : ℕ}
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (f : Model.Space d → ℝ) (hf : Model.InFunctionClass f Δ L ρ) :
    Model.Success (acceleratedAlgorithm d ε L ρ) f ε (acceleratedBudget ε Δ L ρ) = Set.univ := by
  ext u
  cases u
  simp only [Model.Success, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact accelerated_algorithm_correct hε hL hρ haccuracy f hf

theorem accelerated_success_probability {d : ℕ}
    (hε : 0 < ε) (hL : 0 < L) (hρ : 0 < ρ) (haccuracy : ε ≤ L ^ 2 / ρ)
    (f : Model.Space d → ℝ) (hf : Model.InFunctionClass f Δ L ρ)
    (ν : Measure Unit) [IsProbabilityMeasure ν] :
    ν (Model.Success (acceleratedAlgorithm d ε L ρ) f ε (acceleratedBudget ε Δ L ρ)) = 1 := by
  rw [accelerated_success_eq_univ hε hL hρ haccuracy f hf, measure_univ]

end

end RandomizedFO2003.Accelerated
