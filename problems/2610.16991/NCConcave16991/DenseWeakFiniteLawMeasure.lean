import NCConcave16991.DenseWeakFiniteEntropy
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Finite probability masses as actual probability measures -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {I : Type*} [Fintype I]

def toPMF (P : FiniteLaw I) : PMF I :=
  PMF.ofFintype (fun i ↦ ENNReal.ofReal (P.mass i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ P.nonneg i), P.sum_one, ENNReal.ofReal_one])

theorem toPMF_apply (P : FiniteLaw I) (i : I) : P.toPMF i = ENNReal.ofReal (P.mass i) := rfl

variable [MeasurableSpace I] [MeasurableSingletonClass I]

def law (P : FiniteLaw I) : Measure I := P.toPMF.toMeasure

instance law_probability (P : FiniteLaw I) : IsProbabilityMeasure P.law := by
  unfold law
  infer_instance

theorem law_singleton_real (P : FiniteLaw I) (i : I) : P.law.real {i} = P.mass i := by
  change (P.toPMF.toMeasure {i}).toReal = _
  rw [P.toPMF.toMeasure_apply_singleton i (measurableSet_singleton i),
    toPMF_apply, ENNReal.toReal_ofReal (P.nonneg i)]

theorem integral_eq_sum (P : FiniteLaw I) (f : I → ℝ) :
    (∫ i, f i ∂P.law) = ∑ i, P.mass i * f i := by
  unfold law
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [toPMF_apply, ENNReal.toReal_ofReal (P.nonneg i)]
  rfl

theorem event_probability (P : FiniteLaw I) (E : Set I) :
    P.law.real E = ∑ i, E.indicator P.mass i := by
  classical
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← integral_indicator_one hE, integral_eq_sum]
  simp only [Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]

end NCConcave16991.DenseWeakHiding.FiniteLaw
