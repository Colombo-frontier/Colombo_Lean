import MasterWeights254
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper254

/-- A finite oblivious hard-instance distribution gives one deterministic
instance, chosen outside the expectation over the learner's random seed. -/
theorem finite_oblivious_derandomization {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ProbabilityWeights ι) (R : ι → Ω → ℝ) (c : ℝ)
    (hR : ∀ i, Integrable (R i) μ)
    (hbound : ∀ ω, c ≤ ∑ i, p.weight i*R i ω) :
    ∃ i, c ≤ ∫ ω, R i ω ∂μ := by
  classical
  have hs : Integrable (fun ω => ∑ i, p.weight i*R i ω) μ := by
    apply integrable_finset_sum
    intro i _
    exact (hR i).const_mul (p.weight i)
  have hint := integral_mono (integrable_const c) hs hbound
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hint
  rw [integral_finset_sum _ (fun i _ => (hR i).const_mul (p.weight i))] at hint
  simp_rw [integral_const_mul] at hint
  by_contra hn
  push_neg at hn
  obtain ⟨j,hj⟩ := p.exists_positive
  have hstrict : (∑ i, p.weight i*(∫ ω, R i ω ∂μ)) < ∑ i, p.weight i*c := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hn i).le (p.nonneg i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (hn j) hj⟩
  rw [← Finset.sum_mul, p.total, one_mul] at hstrict
  linarith

end Paper254
#print axioms Paper254.finite_oblivious_derandomization
