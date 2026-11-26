import Nonsmooth.ResponseHistoryEncoding

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

def recursiveSupportBeliefData (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) :
    (n : ℕ) → {κ : Kernel (ResponseHistory k n) (Fin k → E) // IsMarkovKernel κ}
  | 0 => ⟨Kernel.const _ Q, inferInstance⟩
  | n + 1 => by
    let old := recursiveSupportBeliefData Q u hu n
    letI : IsMarkovKernel old.val := old.property
    exact ⟨(supportPosteriorUpdate old.val (u n) (hu n)).comap responseHistorySplit
      responseHistorySplit_measurable, inferInstance⟩

def recursiveSupportBelief (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Kernel (ResponseHistory k n) (Fin k → E) := (recursiveSupportBeliefData Q u hu n).val

instance recursiveSupportBelief_markov (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    IsMarkovKernel (recursiveSupportBelief Q u hu n) := (recursiveSupportBeliefData Q u hu n).property

theorem recursiveSupportBelief_zero (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (h : ResponseHistory k 0) :
    recursiveSupportBelief Q u hu 0 h = Q := rfl

theorem recursiveSupportBelief_succ (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n))
    (n : ℕ) (h : ResponseHistory k n) (y : Fin k × ℝ) :
    recursiveSupportBelief Q u hu (n + 1) (responseHistoryJoin (h, y)) =
      supportPosteriorUpdate (recursiveSupportBelief Q u hu n) (u n) (hu n) (h, y) := by
  change supportPosteriorUpdate (recursiveSupportBelief Q u hu n) (u n) (hu n)
    (responseHistorySplit (responseHistoryJoin (h, y))) = _
  rw [responseHistorySplit_join]

end
end Nonsmooth
