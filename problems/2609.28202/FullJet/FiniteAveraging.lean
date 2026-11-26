import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

namespace FullJet

/-- Integrating a pointwise count of failures over an arbitrary random seed. -/
theorem sum_failure_probabilities_ge {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (c : ℝ)
    (hc : ∀ ω, c ≤ ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) :
    c ≤ ∑ i, P.real (A i) := by
  have hi (i : ι) : Integrable ((A i).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hA i)
  have h := integral_mono (integrable_const c) (integrable_finset_sum _ (fun i hi' => hi i)) hc
  simpa only [integral_const, measureReal_univ_eq_one, one_smul,
    integral_finset_sum _ (fun i hi' => hi i), integral_indicator_const _ (hA _),
    smul_eq_mul, mul_one, one_mul] using h

/-- A finite hard distribution gives a fixed hard instance, without a separate
minimax axiom. The seed space and its probability measure are arbitrary. -/
theorem exists_failure_probability_ge {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (δ : ℝ)
    (hcount : ∀ ω, (Fintype.card ι : ℝ) * δ ≤
      ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) :
    ∃ i, δ ≤ P.real (A i) := by
  have hsum := sum_failure_probabilities_ge P A hA _ hcount
  by_contra h
  push_neg at h
  have hlt : ∑ i, P.real (A i) < ∑ _i : ι, δ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i hi => h i)
  simpa using (not_lt_of_ge hsum (by simpa using hlt))

end FullJet
