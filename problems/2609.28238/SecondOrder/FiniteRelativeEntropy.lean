import SecondOrder.FiniteMean
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Finite relative entropy. The measure-theoretic identification below
requires the reference mass to be positive at every point. -/
def pmfKL {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, (p a).toReal*Real.log ((p a).toReal/(q a).toReal)

section FiniteMeasure
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_absolutelyContinuous (p q : PMF α) (hq : ∀ a, q a ≠ 0) :
    p.toMeasure ≪ q.toMeasure := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro a ha
    have h := measure_mono (μ := q.toMeasure) (Set.singleton_subset_iff.mpr ha)
    rw [PMF.toMeasure_apply_singleton q a (measurableSet_singleton a), hs] at h
    exact hq a (le_zero_iff.mp h)
  simp [he]

theorem pmf_rnDeriv (p q : PMF α) (hq : ∀ a, q a ≠ 0) (a : α) :
    p.toMeasure.rnDeriv q.toMeasure a = p a/q a := by
  have h := Measure.setLIntegral_rnDeriv (pmf_absolutelyContinuous p q hq) {a}
  rw [lintegral_singleton, PMF.toMeasure_apply_singleton q a (measurableSet_singleton a),
    PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)] at h
  exact (ENNReal.eq_div_iff (hq a) (q.apply_ne_top a)).mpr (by simpa [mul_comm] using h)

theorem pmf_llr (p q : PMF α) (hq : ∀ a, q a ≠ 0) (a : α) :
    llr p.toMeasure q.toMeasure a = Real.log ((p a).toReal/(q a).toReal) := by
  rw [llr, pmf_rnDeriv p q hq, ENNReal.toReal_div]

/-- The finite sum is the actual Kullback-Leibler divergence of the
associated probability measures, not a separately assumed information cost. -/
theorem klDiv_pmf (p q : PMF α) (hq : ∀ a, q a ≠ 0) :
    klDiv p.toMeasure q.toMeasure = ENNReal.ofReal (pmfKL p q) := by
  rw [klDiv_of_ac_of_integrable (pmf_absolutelyContinuous p q hq) Integrable.of_finite]
  simp only [measureReal_univ_eq_one, add_sub_cancel_right]
  congr 1
  rw [PMF.integral_eq_sum]
  exact Finset.sum_congr rfl (fun a _ => by rw [pmf_llr p q hq]; rfl)

theorem pmfKL_nonneg (p q : PMF α) (hq : ∀ a, q a ≠ 0) : 0 ≤ pmfKL p q := by
  have h := integral_llr_add_sub_measure_univ_nonneg
    (pmf_absolutelyContinuous p q hq) (show Integrable (llr p.toMeasure q.toMeasure) p.toMeasure
      from Integrable.of_finite)
  simpa only [measureReal_univ_eq_one, add_sub_cancel_right, PMF.integral_eq_sum,
    pmf_llr p q hq, smul_eq_mul, pmfKL] using h

end FiniteMeasure

end
end SecondOrder
