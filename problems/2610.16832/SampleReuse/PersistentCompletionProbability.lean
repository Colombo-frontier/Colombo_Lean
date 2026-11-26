import SampleReuse.PersistentPathwiseTransfer
import SampleReuse.PersistentFarProbability
import SecondOrder.SequentialStageCounting

open SecondOrder
open scoped Classical BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {H S : Type}

def persistentOutputProgress (P : PersistentFirstOrderPolicy d T H S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (N : ℕ) : ℕ :=
  max (persistentComparisonRun P Θ A β table N).1 (persistentComparisonIndex P Θ A β table N)

theorem persistentOutputProgress_as_tape (P : PersistentFirstOrderPolicy d T H S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (N : ℕ) :
    persistentOutputProgress P Θ A β table N = firstOrderComparisonOutputProgress
      (persistentPointPolicy P) Θ A β (persistentComparisonTape P Θ A β table) N := by
  simp only [persistentOutputProgress,firstOrderComparisonOutputProgress,
    persistentComparisonRun_as_tape,persistentComparisonIndex_as_tape]

def persistentStageReached (P : PersistentFirstOrderPolicy d T H S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (i : Fin (T+1)) (N : ℕ) : Prop :=
  firstOrderStageReached (persistentPointPolicy P) Θ A β
    (persistentComparisonTape P Θ A β table) i N

/-- Counting under the actual once-sampled source law. The probabilistic
premise is the per-stage bound proved separately by entry resampling. -/
theorem persistent_completion_probability [Fintype H]
    (P : PersistentFirstOrderPolicy d T H S) (hT : 0 < T)
    (A β R : ℝ) (hR : 2 ≤ R) (cap N : ℕ) (hcap0 : 0 < cap)
    (hbudget : 2*N ≤ T*cap)
    (hfast : ∀ i : Fin T,
      pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
        (persistentStageReached P (persistentSourceHidden w) A β (persistentSourceTable w) i.succ N ∧
          persistentStageResponseCount P (persistentSourceHidden w) A β
            (persistentSourceTable w) (i.val+1) N < cap)) ≤ 1/32) :
    pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
      (persistentOutputProgress P (persistentSourceHidden w) A β (persistentSourceTable w) N = T+1)) ≤
      1/16 := by
  apply sequential_completion_probability (persistentSourceLaw d T H R hR) hT hcap0
    (fun i : Fin T => fun w => persistentStageResponseCount P (persistentSourceHidden w) A β
      (persistentSourceTable w) (i.val+1) N)
    (fun i : Fin T => fun w => decide (persistentStageReached P (persistentSourceHidden w) A β
      (persistentSourceTable w) i.succ N))
    (fun w => decide (persistentOutputProgress P (persistentSourceHidden w) A β
      (persistentSourceTable w) N = T+1))
  · intro w hc i
    simp only [decide_eq_true_eq] at hc ⊢
    rw [persistentOutputProgress_as_tape] at hc
    exact firstOrderComparison_complete_reached (persistentPointPolicy P) _ A β _ N hc i.succ
  · intro w
    exact persistentStageResponseCount_budget P _ A β _ N
  · exact hbudget
  · intro i
    simpa only [decide_eq_true_eq] using hfast i

end
end SampleReuse
