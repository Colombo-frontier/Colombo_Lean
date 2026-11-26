import Bilevel.Transcript
import Bilevel.UnboundedStopping

/-!
# An adaptive two-oracle testing reduction

This module combines the actual state-machine coupling with genuine
probability/expectation bounds for unbounded integrable stopping counts.
Common output before activation is proved from the program recursion.
The measurable stopping count, integrable losses, and independence of each
fresh activation bit from the decision to make that call are explicit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.AdaptiveTesting

variable {Ω State Query Observation Output : Type*}

/-- Terminal output of the recursive adaptive execution on a random outcome. -/
def terminal (query : State → Query) (update : State → Observation → State)
    (oracle : Query → Bool → Observation) (draws : Ω → ℕ → Bool)
    (initial : Ω → State) (output : State → Output) (N : Ω → ℕ) (ω : Ω) : Output :=
  output (Transcript.run query update oracle (draws ω) (initial ω) (N ω))

/-- The two executions are allowed to have different stopping counts. Their
shared inactive responses, actual first-halt conditions, and fresh-bit laws
imply the expected-query lower bound. No common-output premise is assumed. -/
theorem adaptive_testing_bound
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (query : State → Query) (update : State → Observation → State)
    (oraclePlus oracleMinus : Query → Bool → Observation)
    (inactive : ∀ q, oraclePlus q false = oracleMinus q false)
    (draws : Ω → ℕ → Bool) (initial : Ω → State)
    (halt : State → Bool) (output : State → Output) (NPlus NMinus : Ω → ℕ)
    (firstPlus : ∀ ω, Transcript.FirstHalt halt
      (Transcript.run query update oraclePlus (draws ω) (initial ω)) (NPlus ω))
    (firstMinus : ∀ ω, Transcript.FirstHalt halt
      (Transcript.run query update oracleMinus (draws ω) (initial ω)) (NMinus ω))
    (hN : Measurable NPlus) (hNi : Integrable (fun ω => (NPlus ω : ℝ)) μ)
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (fresh_measurable : ∀ t, MeasurableSet {ω | draws ω t = true})
    (fresh_independent : ∀ t, IndepSet (UnboundedStopping.query NPlus t)
      {ω | draws ω t = true} μ)
    (fresh_probability : ∀ t, μ.real {ω | draws ω t = true} = p)
    (lossPlus lossMinus : Output → ℝ)
    (plus_nonneg : ∀ x, 0 ≤ lossPlus x) (minus_nonneg : ∀ x, 0 ≤ lossMinus x)
    (separation : ∀ x, 2 * γ ≤ lossPlus x + lossMinus x)
    (plus_integrable : Integrable (fun ω => lossPlus
      (terminal query update oraclePlus draws initial output NPlus ω)) μ)
    (minus_integrable : Integrable (fun ω => lossMinus
      (terminal query update oracleMinus draws initial output NMinus ω)) μ)
    (accuracy : ((∫ ω, lossPlus (terminal query update oraclePlus draws initial output NPlus ω) ∂μ)
      + ∫ ω, lossMinus (terminal query update oracleMinus draws initial output NMinus ω) ∂μ) / 2
        ≤ γ / 8) :
    7 / (8 * p) ≤ ∫ ω, (NPlus ω : ℝ) ∂μ := by
  let activation : ℕ → Set Ω := fun t =>
    UnboundedStopping.query NPlus t ∩ {ω | draws ω t = true}
  have activation_measurable : ∀ t, MeasurableSet (activation t) := fun t =>
    (UnboundedStopping.query_measurable hN t).inter (fresh_measurable t)
  have factorization : ∀ t,
      μ.real (activation t) = p * μ.real (UnboundedStopping.query NPlus t) := fun t =>
    StoppedOracle.fresh_factorization _ _ p (fresh_independent t) (fresh_probability t)
  apply UnboundedStopping.testing_bound hN hNi activation activation_measurable hp hγ
    factorization plus_integrable minus_integrable
    (fun ω => plus_nonneg _) (fun ω => minus_nonneg _)
    ?_ accuracy
  intro ω hω
  have no_activation : ∀ t < NPlus ω, draws ω t = false := by
    intro t ht
    cases hb : draws ω t with
    | false => rfl
    | true =>
      exfalso
      exact hω (Set.mem_iUnion.mpr ⟨t, ht, hb⟩)
  have heq := (Transcript.stopped_outputs_equal query update oraclePlus oracleMinus inactive
    (draws ω) (initial ω) halt output (firstPlus ω) (firstMinus ω) no_activation).2
  change terminal query update oraclePlus draws initial output NPlus ω =
    terminal query update oracleMinus draws initial output NMinus ω at heq
  rw [heq]
  exact separation _

end Bilevel.AdaptiveTesting
