import FullJet.FiniteProbability
import FullJet.FiniteAveraging

open MeasureTheory Set
open scoped BigOperators

namespace FullJet

/-- The latent finite sample has one fixed law, independent of the seed. -/
theorem pmf_seed_event_integrable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : PMF ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    Integrable (fun ω => (p.toOuterMeasure {i | ω ∈ A i}).toReal) P := by
  classical
  have heq : (fun ω => (p.toOuterMeasure {i | ω ∈ A i}).toReal) =
      fun ω => ∑ i, (A i).indicator (fun _ => (p i).toReal) ω := by
    funext ω
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
      pmf_event_toReal p {i | ω ∈ A i}
  rw [heq]
  exact integrable_finset_sum _ (fun i _ => (integrable_const _).indicator (hA i))

/-- Finite averaging and integration over an arbitrary independent seed
commute. Only the actual event for each fixed instance must be measurable. -/
theorem pmf_seed_event_integral {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : PMF ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    (∫ ω, (p.toOuterMeasure {i | ω ∈ A i}).toReal ∂P) =
      ∑ i, (p i).toReal * P.real (A i) := by
  classical
  have heq : (fun ω => (p.toOuterMeasure {i | ω ∈ A i}).toReal) =
      fun ω => ∑ i, (A i).indicator (fun _ => (p i).toReal) ω := by
    funext ω
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
      pmf_event_toReal p {i | ω ∈ A i}
  rw [heq, integral_finset_sum _ (fun i _ => (integrable_const _).indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_indicator_const _ (hA i), smul_eq_mul, mul_comm]

theorem pmf_seed_event_average_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : PMF ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (δ : ℝ)
    (hbound : ∀ ω, (p.toOuterMeasure {i | ω ∈ A i}).toReal ≤ δ) :
    ∑ i, (p i).toReal * P.real (A i) ≤ δ := by
  rw [← pmf_seed_event_integral P p A hA]
  have h := integral_mono (pmf_seed_event_integrable P p A hA) (integrable_const δ) hbound
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

/-- A low average success probability yields one fixed supported instance
with at least the complementary failure probability. -/
theorem pmf_exists_low_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : PMF ι) (A : ι → Set Ω) (δ : ℝ)
    (hbound : ∑ i, (p i).toReal * P.real (A i) ≤ δ) :
    ∃ i ∈ p.support, P.real (A i) ≤ δ := by
  classical
  by_contra h
  push_neg at h
  have hle (i : ι) : (p i).toReal * δ ≤ (p i).toReal * P.real (A i) := by
    by_cases hi : i ∈ p.support
    · exact mul_le_mul_of_nonneg_left (h i hi).le ENNReal.toReal_nonneg
    · simp [(p.apply_eq_zero_iff i).mpr hi]
  obtain ⟨i, hi⟩ := p.support_nonempty
  have hpi : 0 < (p i).toReal := ENNReal.toReal_pos ((p.mem_support_iff i).mp hi) (p.apply_ne_top i)
  have hs := Finset.sum_lt_sum (fun j _ => hle j)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (h i hi) hpi⟩
  rw [← Finset.sum_mul, pmf_toReal_sum p, one_mul] at hs
  exact (not_lt_of_ge hbound) hs

end FullJet
