import Bilevel.BernoulliOracle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Basic

/-!
# Finite-horizon activation counting and two-hypothesis testing

All expectations and probabilities here are genuine integrals and measures.
Query events may depend on previous responses. Freshness is expressed by
`IndepSet (query i) (fresh i)`; constructing a filtration and deriving this
independence for the manuscript's original SFO model remains a separate task.
There is no unbounded-stopping-time claim in this module.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Bilevel.StoppedOracle

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Number of events that occur, represented as a real-valued random variable. -/
def count (events : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i, (events i).indicator (fun _ => (1 : ℝ)) ω

theorem integral_count (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i)) :
    (∫ ω, count events ω ∂μ) = ∑ i, μ.real (events i) := by
  classical
  unfold count
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl (fun i _ => integral_indicator_one (hmeas i))
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hmeas i)

/-- Linearity of expectation gives the finite predictable-counting identity.
The factorization premise is the precise one-step freshness condition needed. -/
theorem expected_activation_count
    (query activation : ι → Set Ω) (p : ℝ)
    (hq : ∀ i, MeasurableSet (query i))
    (ha : ∀ i, MeasurableSet (activation i))
    (factorization : ∀ i, μ.real (activation i) = p * μ.real (query i)) :
    (∫ ω, count activation ω ∂μ) = p * ∫ ω, count query ω ∂μ := by
  rw [integral_count activation ha, integral_count query hq, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => factorization i)

omit [IsProbabilityMeasure μ] in
/-- The factorization follows from actual event independence, rather than an
axiom about an unspecified expectation functional. -/
theorem fresh_factorization (query fresh : Set Ω) (p : ℝ)
    (hind : IndepSet query fresh μ) (hprob : μ.real fresh = p) :
    μ.real (query ∩ fresh) = p * μ.real query := by
  rw [measureReal_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul]
  change μ.real query * μ.real fresh = p * μ.real query
  rw [hprob, mul_comm]

theorem expected_fresh_activation_count
    (query fresh : ι → Set Ω) (p : ℝ)
    (hq : ∀ i, MeasurableSet (query i))
    (hf : ∀ i, MeasurableSet (fresh i))
    (hind : ∀ i, IndepSet (query i) (fresh i) μ)
    (hprob : ∀ i, μ.real (fresh i) = p) :
    (∫ ω, count (fun i => query i ∩ fresh i) ω ∂μ) =
      p * ∫ ω, count query ω ∂μ := by
  apply expected_activation_count query (fun i => query i ∩ fresh i) p hq
    (fun i => (hq i).inter (hf i))
  intro i
  exact fresh_factorization (query i) (fresh i) p (hind i) (hprob i)

/-- Probability of any activation is bounded by expected activation count. -/
theorem activation_probability_le_count
    (activation : ι → Set Ω) (ha : ∀ i, MeasurableSet (activation i)) :
    μ.real (⋃ i, activation i) ≤ ∫ ω, count activation ω ∂μ := by
  rw [integral_count activation ha]
  exact measureReal_iUnion_fintype_le activation

/-- The no-activation event survives with probability at least `1 - p E N`. -/
theorem no_activation_probability
    (query activation : ι → Set Ω) (p : ℝ)
    (hq : ∀ i, MeasurableSet (query i))
    (ha : ∀ i, MeasurableSet (activation i))
    (factorization : ∀ i, μ.real (activation i) = p * μ.real (query i)) :
    1 - μ.real (⋃ i, activation i)ᶜ ≤ p * ∫ ω, count query ω ∂μ := by
  have hc := activation_probability_le_count activation ha (μ := μ)
  rw [expected_activation_count query activation p hq ha factorization] at hc
  rw [measureReal_compl (MeasurableSet.iUnion ha)]
  simpa using hc

/-- On a coupled no-information event, pointwise gradient separation forces
average risk. The functions may already be gradients evaluated at two outputs;
their equality on this event is used only to establish `separation`. -/
theorem risk_from_common_event
    {event : Set Ω} (hevent : MeasurableSet event)
    {plus minus : Ω → ℝ} (hplus : Integrable plus μ) (hminus : Integrable minus μ)
    (plus_nonneg : ∀ ω, 0 ≤ plus ω) (minus_nonneg : ∀ ω, 0 ≤ minus ω)
    {γ : ℝ} (separation : ∀ ω ∈ event, 2 * γ ≤ plus ω + minus ω) :
    γ * μ.real event ≤ ((∫ ω, plus ω ∂μ) + ∫ ω, minus ω ∂μ) / 2 := by
  have hbound : ∀ ω, event.indicator (fun _ => 2 * γ) ω ≤ plus ω + minus ω := by
    intro ω
    by_cases hω : ω ∈ event
    · simpa [Set.indicator_of_mem hω] using separation ω hω
    · simp only [Set.indicator_of_not_mem hω]
      exact add_nonneg (plus_nonneg ω) (minus_nonneg ω)
  have hi := integral_mono ((integrable_const (2 * γ)).indicator hevent)
    (hplus.add hminus) hbound
  simp only [Pi.add_apply] at hi
  rw [integral_indicator_const _ hevent, integral_add hplus hminus] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

/-- A common output on the no-information event and global loss separation
suffice for the preceding integral risk bound. -/
theorem risk_from_coupled_outputs
    {X : Type*} (lossPlus lossMinus : X → ℝ) (outputPlus outputMinus : Ω → X)
    {event : Set Ω} (hevent : MeasurableSet event) {γ : ℝ}
    (hplus : Integrable (fun ω => lossPlus (outputPlus ω)) μ)
    (hminus : Integrable (fun ω => lossMinus (outputMinus ω)) μ)
    (plus_nonneg : ∀ x, 0 ≤ lossPlus x) (minus_nonneg : ∀ x, 0 ≤ lossMinus x)
    (separation : ∀ x, 2 * γ ≤ lossPlus x + lossMinus x)
    (common_output : ∀ ω ∈ event, outputPlus ω = outputMinus ω) :
    γ * μ.real event ≤
      ((∫ ω, lossPlus (outputPlus ω) ∂μ) + ∫ ω, lossMinus (outputMinus ω) ∂μ) / 2 := by
  apply risk_from_common_event hevent hplus hminus
    (fun ω => plus_nonneg _) (fun ω => minus_nonneg _)
  intro ω hω
  rw [common_output ω hω]
  exact separation (outputMinus ω)

/-- Finite-horizon expected-query lower bound with all measure assumptions
visible. The coupling is supplied as the gradient separation on the common
no-activation event; it is not asserted for arbitrary algorithms here. -/
theorem finite_horizon_testing_bound
    (query activation : ι → Set Ω) {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (hq : ∀ i, MeasurableSet (query i))
    (ha : ∀ i, MeasurableSet (activation i))
    (factorization : ∀ i, μ.real (activation i) = p * μ.real (query i))
    {plus minus : Ω → ℝ} (hplus : Integrable plus μ) (hminus : Integrable minus μ)
    (plus_nonneg : ∀ ω, 0 ≤ plus ω) (minus_nonneg : ∀ ω, 0 ≤ minus ω)
    (separation : ∀ ω ∈ (⋃ i, activation i)ᶜ, 2 * γ ≤ plus ω + minus ω)
    (accuracy : ((∫ ω, plus ω ∂μ) + ∫ ω, minus ω ∂μ) / 2 ≤ γ / 8) :
    7 / (8 * p) ≤ ∫ ω, count query ω ∂μ := by
  exact BernoulliOracle.expected_queries_from_testing hp hγ
    (risk_from_common_event (MeasurableSet.iUnion ha).compl hplus hminus
      plus_nonneg minus_nonneg separation)
    (no_activation_probability query activation p hq ha factorization) accuracy

end Bilevel.StoppedOracle
