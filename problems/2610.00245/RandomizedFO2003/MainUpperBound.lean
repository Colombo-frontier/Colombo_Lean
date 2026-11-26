import RandomizedFO2003.AcceleratedAlgorithmCorrectness

namespace RandomizedFO2003.Model

/-- Dimension-uniform upper bound in the original first-order model.
The algorithm and fixed integer budget are chosen before the objective.
The deterministic success guarantee is stronger than probability 2/3. -/
def MainUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ ε Δ L₁ L₂ : ℝ, 0 < ε → 0 < Δ → 0 < L₁ → 0 < L₂ →
      ε ≤ L₁ ^ 2 / L₂ →
      1 ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)) →
      ∀ d : ℕ, ∃ T : ℕ, ∃ A : Algorithm d Unit,
        (T : ℝ) ≤ C * rate ε Δ L₁ L₂ ∧
          ∀ f : Space d → ℝ, InFunctionClass f Δ L₁ L₂ →
            ‖gradient f (A.output T () (transcript A f () T))‖ ≤ ε

/-- The accelerated upper bound, including integer rounding, the final
epoch, measurable oracle implementation, and exact transcript simulation. -/
theorem main_upper_bound : MainUpperBound := by
  refine ⟨(512 : ℝ) ^ (7 / 4 : ℝ), by positivity, ?_⟩
  intro ε Δ L₁ L₂ hε _hΔ hL₁ hL₂ haccuracy hmass d
  exact ⟨Accelerated.acceleratedBudget ε Δ L₁ L₂, Accelerated.acceleratedAlgorithm d ε L₁ L₂,
    Accelerated.accelerated_budget_le_rate hε hL₁ hL₂ hmass,
    fun f hf => Accelerated.accelerated_algorithm_correct hε hL₁ hL₂ haccuracy f hf⟩

end RandomizedFO2003.Model
