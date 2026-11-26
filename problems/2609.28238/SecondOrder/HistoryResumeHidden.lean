import SecondOrder.HistoryHiddenEquiv
import SecondOrder.HistoryRebase

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- Reconstruct the original full history after restarting at a public
entry history with a separately stored hidden parameter. -/
def historyResumeHidden (n : ℕ) : (k : ℕ) →
    FiniteHistory (H × FiniteHistory S A n) A k → FiniteHistory (H × S) A (n+k)
  | 0, h => historyJoinHidden n h
  | k+1, h => (historyResumeHidden n k h.1,h.2)

theorem historyResumeHidden_measurable (n : ℕ) : ∀ k,
    Measurable (historyResumeHidden (H := H) (S := S) (A := A) n k) := by
  intro k
  induction k with
  | zero => exact historyJoinHidden_measurable n
  | succ k ih => exact (ih.comp measurable_fst).prodMk measurable_snd

theorem historyResumeHidden_initial (n : ℕ) : ∀ k (h : FiniteHistory (H × FiniteHistory S A n) A k),
    (finiteHistoryInitial (n+k) (historyResumeHidden n k h)).1=(finiteHistoryInitial k h).1 := by
  intro k
  induction k with
  | zero => exact historyJoinHidden_initial n
  | succ k ih => intro h; exact ih h.1

theorem historyResumeHidden_public (n : ℕ) : ∀ k (h : FiniteHistory (H × FiniteHistory S A n) A k),
    finiteHistoryMapInitial (Prod.snd : H × S → S) (n+k) (historyResumeHidden n k h)=
      historyRebase n k (finiteHistoryMapInitial Prod.snd k h) := by
  intro k
  induction k with
  | zero => exact historyJoinHidden_public n
  | succ k ih => intro h; exact Prod.ext (ih h.1) rfl

theorem historyResumeHidden_eq_rebase (n : ℕ) : ∀ k (h : FiniteHistory (H × FiniteHistory S A n) A k),
    historyResumeHidden n k h=historyRebase n k (finiteHistoryMapInitial (historyJoinHidden n) k h) := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih => intro h; exact Prod.ext (ih h.1) rfl

def resumedHiddenKernel (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A) (n k : ℕ) :
    Kernel (FiniteHistory (H × FiniteHistory S A n) A k) A :=
  (K (n+k)).comap (historyResumeHidden n k) (historyResumeHidden_measurable n k)

instance resumedHiddenKernel_markov (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (n k : ℕ) : IsMarkovKernel (resumedHiddenKernel K n k) := by
  unfold resumedHiddenKernel
  infer_instance

end
end SecondOrder
