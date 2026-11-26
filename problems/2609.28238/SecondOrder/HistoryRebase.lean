import SecondOrder.KernelContinuation
import SecondOrder.KernelHiddenIndependence

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A X : Type u} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace X]

/-- Treat the complete entry history as the new initial state and retain
all subsequent replies in their original order. -/
def historyRebase (n : ℕ) : (k : ℕ) → FiniteHistory (FiniteHistory S A n) A k → FiniteHistory S A (n+k)
  | 0, h => h
  | k+1, h => (historyRebase n k h.1,h.2)

def historyUnbase (n : ℕ) : (k : ℕ) → FiniteHistory S A (n+k) → FiniteHistory (FiniteHistory S A n) A k
  | 0, h => h
  | k+1, h => (historyUnbase n k h.1,h.2)

theorem historyUnbase_rebase (n : ℕ) : ∀ k (h : FiniteHistory (FiniteHistory S A n) A k),
    historyUnbase n k (historyRebase n k h)=h := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih => intro h; exact Prod.ext (ih h.1) rfl

theorem historyRebase_unbase (n : ℕ) : ∀ k (h : FiniteHistory S A (n+k)),
    historyRebase n k (historyUnbase n k h)=h := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih => intro h; exact Prod.ext (ih h.1) rfl

theorem historyRebase_measurable (n : ℕ) : ∀ k, Measurable (historyRebase (S := S) (A := A) n k) := by
  intro k
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact (ih.comp measurable_fst).prodMk measurable_snd

theorem historyUnbase_measurable (n : ℕ) : ∀ k, Measurable (historyUnbase (S := S) (A := A) n k) := by
  intro k
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact (ih.comp measurable_fst).prodMk measurable_snd

def historyRebaseEquiv (n k : ℕ) : FiniteHistory (FiniteHistory S A n) A k ≃ᵐ FiniteHistory S A (n+k) where
  toFun := historyRebase n k
  invFun := historyUnbase n k
  left_inv := historyUnbase_rebase n k
  right_inv := historyRebase_unbase n k
  measurable_toFun := historyRebase_measurable n k
  measurable_invFun := historyUnbase_measurable n k

theorem historyRebase_initial (n : ℕ) : ∀ k (h : FiniteHistory (FiniteHistory S A n) A k),
    finiteHistoryInitial (n+k) (historyRebase n k h)=finiteHistoryInitial n (finiteHistoryInitial k h) := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih => intro h; exact ih h.1

def rebasedQuery (query : ∀ n, FiniteHistory S A n → X) (n k : ℕ) :
    FiniteHistory (FiniteHistory S A n) A k → X := query (n+k) ∘ historyRebase n k

theorem rebasedQuery_measurable (query : ∀ n, FiniteHistory S A n → X)
    (hq : ∀ n, Measurable (query n)) (n k : ℕ) : Measurable (rebasedQuery query n k) :=
  (hq (n+k)).comp (historyRebase_measurable n k)

def rebasedResponseKernel (K : ∀ n, Kernel (FiniteHistory S A n) A) (n k : ℕ) :
    Kernel (FiniteHistory (FiniteHistory S A n) A k) A :=
  (K (n+k)).comap (historyRebase n k) (historyRebase_measurable n k)

instance rebasedResponseKernel_markov (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n k : ℕ) : IsMarkovKernel (rebasedResponseKernel K n k) := by
  unfold rebasedResponseKernel
  infer_instance

end
end SecondOrder
