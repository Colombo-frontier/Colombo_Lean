import FreshGradientMinimax.EpochProgram
import FreshGradientMinimax.ValueWorkRate

/-! A single original-query program for all epochs of the value solver.
Its stopped output and actual call count have exactly the previously
analysed costed law. These theorems fix the objective and known gradient
function. ParameterAccuracy extends them to jointly measurable random
known regularizers; random base objectives and final budget truncation
remain separate obligations. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def valueRunProgram (dx dy : ℕ) (ℓ α σ m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : ℕ → OracleProgram dx dy (Joint dx dy) (Joint dx dy)
  | 0 => OracleProgram.pure id measurable_id
  | n + 1 => (valueRunProgram dx dy ℓ α σ m H e E₀ r hr n).chain
      (fullEpochProgram dx dy ℓ α σ m H e (valueEnvelope E₀ e n) r hr)

def valueSolverProgram (dx dy : ℕ) (ℓ α σ m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : OracleProgram dx dy (Joint dx dy) (Joint dx dy) :=
  valueRunProgram dx dy ℓ α σ m H e E₀ r hr (finalEpochIndex E₀ e + 1)

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem valueRunProgram_law (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (n : ℕ) :
    (valueRunProgram dx dy ℓ α σ m H e E₀ r hr n).lawKernel O.kernel = S.costedValueRunKernel O m H e E₀ r hr n := by
  induction n with
  | zero => rw [valueRunProgram, OracleProgram.pure_law]; rfl
  | succ n ih => rw [valueRunProgram, OracleProgram.chain_law, S.fullEpochProgram_law, ih, costedValueRunKernel]

theorem valueSolverProgram_law (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).lawKernel O.kernel = S.costedValueSolverKernel O m H e E₀ r hr :=
  S.valueRunProgram_law O m H e E₀ r hr _

theorem valueSolverProgram_original (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    (valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel =
      S.costedValueSolverKernel O m H e E₀ r hr := by
  rw [OracleProgram.originalKernel_eq_law, S.valueSolverProgram_law]

theorem valueSolverProgram_output (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Joint dx dy)) :
    ((valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν).map Prod.fst =
      S.valueSolverKernel O m H e E₀ r hr ∘ₘ ν := by
  rw [S.valueSolverProgram_original, S.costedValueSolverKernel_output_law]

theorem valueSolverProgram_mean_calls (O : FreshOracle S.toNCObjective σ) (m H e E₀ : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    Integrable costValue ((valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, costValue t ∂(valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) =
      valueSolverWork ℓ α σ m H e E₀ := by
  rw [S.valueSolverProgram_original]
  exact S.costedValueSolverKernel_random_cost O m H e E₀ r hr ν

theorem valueSolverProgram_calls_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hHℓ : H ≤ 20 * ℓ)
    (he : 0 < e) (hE₀ : 0 ≤ E₀) (r : Euclid dy → Euclid dy) (hr : Measurable r)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 70 * valueLogFactor ℓ σ m e ^ 3 *
        (Real.sqrt (H / m) * Real.log (2 + E₀ / e) + σ ^ 2 / (m * e)) := by
  rw [S.valueSolverProgram_original]
  exact S.costedValueSolverKernel_random_rate O hfast hm hmH hHℓ he hE₀ r hr ν

theorem valueSolverProgram_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E₀ : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E₀) :
    Integrable (fun t : Joint dx dy × ℕ => Q t.1.2 - Q v)
      ((valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    Integrable (fun t => S.fastError m t.1)
      ((valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ∧
    (∫ t, Q t.1.2 - Q v ∂(valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤ e ∧
    (∫ t, S.fastError m t.1 ∂(valueSolverProgram dx dy ℓ α σ m H e E₀ r hr).originalKernel O.kernel ∘ₘ ν) ≤ e := by
  rw [S.valueSolverProgram_original]
  exact S.costedValueSolverKernel_accuracy O hαℓ hfast hm hmH he r hr model v hmin ν hInit hEnergy

end SCObjective
end FreshGradientMinimax
