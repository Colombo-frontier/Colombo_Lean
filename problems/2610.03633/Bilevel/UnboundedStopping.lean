import Bilevel.StoppedOracle

/-!
# Unbounded integrable query counts

The query count `N : Ω → ℕ` is finite on each outcome but need not have any
deterministic upper bound. Countable continuity of probability, applied to
finite query-index sets, proves the no-activation inequality. The one-step
factorization is explicit; the last theorem derives it from event independence.
No adaptive SFO execution or filtration is assumed to exist implicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Bilevel.UnboundedStopping

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The event that call `t` is made; calls are numbered starting from zero. -/
def query (N : Ω → ℕ) (t : ℕ) : Set Ω := {ω | t < N ω}

/-- Count only calls whose indices belong to a finite set. -/
def partialCount (N : Ω → ℕ) (s : Finset ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ s, (query N t).indicator (fun _ => (1 : ℝ)) ω

theorem query_measurable {N : Ω → ℕ} (hN : Measurable N) (t : ℕ) :
    MeasurableSet (query N t) :=
  measurableSet_lt measurable_const hN

omit [MeasurableSpace Ω] in
theorem partialCount_le (N : Ω → ℕ) (s : Finset ℕ) (ω : Ω) :
    partialCount N s ω ≤ (N ω : ℝ) := by
  classical
  simp only [partialCount, Set.indicator_apply, query, Set.mem_setOf_eq, Finset.sum_boole]
  have hs : s.filter (fun t => t < N ω) ⊆ Finset.range (N ω) := by
    intro t ht
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
  have hc := Finset.card_le_card hs
  simpa using (Nat.cast_le (α := ℝ)).mpr hc

theorem partialCount_integrable {N : Ω → ℕ} (hN : Measurable N) (s : Finset ℕ) :
    Integrable (partialCount N s) μ := by
  classical
  apply integrable_finset_sum
  intro t _
  exact (integrable_const (1 : ℝ)).indicator (query_measurable hN t)

theorem integral_partialCount {N : Ω → ℕ} (hN : Measurable N) (s : Finset ℕ) :
    (∫ ω, partialCount N s ω ∂μ) = ∑ t ∈ s, μ.real (query N t) := by
  classical
  unfold partialCount
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl (fun t _ => integral_indicator_one (query_measurable hN t))
  · intro t _
    exact (integrable_const (1 : ℝ)).indicator (query_measurable hN t)

theorem finite_activation_bound
    {N : Ω → ℕ} (hN : Measurable N) (hNi : Integrable (fun ω => (N ω : ℝ)) μ)
    (activation : ℕ → Set Ω) {p : ℝ} (hp : 0 ≤ p)
    (factorization : ∀ t, μ.real (activation t) = p * μ.real (query N t))
    (s : Finset ℕ) :
    μ.real (⋃ t ∈ s, activation t) ≤ p * ∫ ω, (N ω : ℝ) ∂μ := by
  calc
    _ ≤ ∑ t ∈ s, μ.real (activation t) := measureReal_biUnion_finset_le s activation
    _ = p * ∑ t ∈ s, μ.real (query N t) := by
      simp_rw [factorization, Finset.mul_sum]
    _ = p * ∫ ω, partialCount N s ω ∂μ := by rw [integral_partialCount hN s]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_mono (partialCount_integrable hN s) hNi (partialCount_le N s)) hp

/-- Countably many possible query indices do not change the activation bound.
This proves the unbounded-count inequality without assuming a fixed horizon. -/
theorem activation_probability_bound
    {N : Ω → ℕ} (hN : Measurable N) (hNi : Integrable (fun ω => (N ω : ℝ)) μ)
    (activation : ℕ → Set Ω) {p : ℝ} (hp : 0 ≤ p)
    (factorization : ∀ t, μ.real (activation t) = p * μ.real (query N t)) :
    μ.real (⋃ t, activation t) ≤ p * ∫ ω, (N ω : ℝ) ∂μ := by
  have hnonneg : 0 ≤ p * ∫ ω, (N ω : ℝ) ∂μ :=
    mul_nonneg hp (integral_nonneg (fun _ => Nat.cast_nonneg _))
  apply ENNReal.toReal_le_of_le_ofReal hnonneg
  rw [measure_iUnion_eq_iSup_accumulate]
  apply iSup_le
  intro n
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnonneg).mpr
  have hf := finite_activation_bound hN hNi activation hp factorization (Finset.range (n + 1))
  simpa only [Set.accumulate_def, Finset.mem_range, Nat.lt_succ_iff] using hf

theorem no_activation_probability
    {N : Ω → ℕ} (hN : Measurable N) (hNi : Integrable (fun ω => (N ω : ℝ)) μ)
    (activation : ℕ → Set Ω) (ha : ∀ t, MeasurableSet (activation t))
    {p : ℝ} (hp : 0 ≤ p)
    (factorization : ∀ t, μ.real (activation t) = p * μ.real (query N t)) :
    1 - μ.real (⋃ t, activation t)ᶜ ≤ p * ∫ ω, (N ω : ℝ) ∂μ := by
  rw [measureReal_compl (MeasurableSet.iUnion ha)]
  simpa using activation_probability_bound hN hNi activation hp factorization

/-- The `7/(8p)` lower bound for a measurable integrable, possibly unbounded,
query count. The coupling/separation obligation remains an explicit premise. -/
theorem testing_bound
    {N : Ω → ℕ} (hN : Measurable N) (hNi : Integrable (fun ω => (N ω : ℝ)) μ)
    (activation : ℕ → Set Ω) (ha : ∀ t, MeasurableSet (activation t))
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    (factorization : ∀ t, μ.real (activation t) = p * μ.real (query N t))
    {plus minus : Ω → ℝ} (hplus : Integrable plus μ) (hminus : Integrable minus μ)
    (plus_nonneg : ∀ ω, 0 ≤ plus ω) (minus_nonneg : ∀ ω, 0 ≤ minus ω)
    (separation : ∀ ω ∈ (⋃ t, activation t)ᶜ, 2 * γ ≤ plus ω + minus ω)
    (accuracy : ((∫ ω, plus ω ∂μ) + ∫ ω, minus ω ∂μ) / 2 ≤ γ / 8) :
    7 / (8 * p) ≤ ∫ ω, (N ω : ℝ) ∂μ := by
  exact BernoulliOracle.expected_queries_from_testing hp hγ
    (StoppedOracle.risk_from_common_event (MeasurableSet.iUnion ha).compl hplus hminus
      plus_nonneg minus_nonneg separation)
    (no_activation_probability hN hNi activation ha hp.le factorization) accuracy

/-- Specialization where activation means a fresh Bernoulli success on a call
actually made. Event independence implies the required one-step factorization. -/
theorem no_fresh_activation_probability
    {N : Ω → ℕ} (hN : Measurable N) (hNi : Integrable (fun ω => (N ω : ℝ)) μ)
    (fresh : ℕ → Set Ω) (hf : ∀ t, MeasurableSet (fresh t)) {p : ℝ} (hp : 0 ≤ p)
    (hind : ∀ t, IndepSet (query N t) (fresh t) μ)
    (hprob : ∀ t, μ.real (fresh t) = p) :
    1 - μ.real (⋃ t, query N t ∩ fresh t)ᶜ ≤ p * ∫ ω, (N ω : ℝ) ∂μ := by
  apply no_activation_probability hN hNi (fun t => query N t ∩ fresh t)
    (fun t => (query_measurable hN t).inter (hf t)) hp
  intro t
  exact StoppedOracle.fresh_factorization (query N t) (fresh t) p (hind t) (hprob t)

end Bilevel.UnboundedStopping
