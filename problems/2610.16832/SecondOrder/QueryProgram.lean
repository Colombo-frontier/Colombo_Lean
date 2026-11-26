import SecondOrder.AdaptiveChordCalls

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- A causal sequence of local routines. A routine may use its newly drawn
sample only in the state update, after its requested cost has been computed. -/
def callRun {S Ω : Type*} (initial : S) (update : ℕ → S → Ω → S) :
    (n : ℕ) → Draws Ω n → S
  | 0, _ => initial
  | n+1, w => update n (callRun initial update n w.1) w.2

def callCost {S Ω : Type*} (initial : S) (request : ℕ → S → ℕ) (update : ℕ → S → Ω → S) :
    (n : ℕ) → Draws Ω n → ℕ :=
  freshHistoryCost (fun n w => request n (callRun initial update n w))

abbrev QueryBudgetState (S : Type*) := S × ℕ × Bool

/-- The fields are program state, calls spent, and whether a request was
rejected. A rejected request does not consume samples or oracle calls. -/
def queryBudgetStep {S Ω : Type*} (Q : ℕ) (request : S → ℕ) (update : S → Ω → S)
    (z : QueryBudgetState S) (ω : Ω) : QueryBudgetState S :=
  if z.2.2 then z
  else if z.2.1+request z.1 ≤ Q then (update z.1 ω,z.2.1+request z.1,false)
  else (z.1,z.2.1,true)

def queryBudgetRun {S Ω : Type*} (Q : ℕ) (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) : (n : ℕ) → Draws Ω n → QueryBudgetState S
  | 0, _ => (initial,0,false)
  | n+1, w => queryBudgetStep Q (request n) (update n) (queryBudgetRun Q initial request update n w.1) w.2

theorem queryBudgetStep_rejected {S Ω : Type*} (Q : ℕ) (request : S → ℕ) (update : S → Ω → S)
    (z : QueryBudgetState S) (hz : z.2.2 = false) (hc : Q < z.2.1+request z.1) (ω : Ω) :
    queryBudgetStep Q request update z ω = (z.1,z.2.1,true) := by
  simp [queryBudgetStep, hz, Nat.not_le.mpr hc]

theorem queryBudgetStep_frozen {S Ω : Type*} (Q : ℕ) (request : S → ℕ) (update : S → Ω → S)
    (z : QueryBudgetState S) (hz : z.2.2 = true) (ω : Ω) :
    queryBudgetStep Q request update z ω = z := by simp [queryBudgetStep, hz]

theorem queryBudgetStep_spent_le {S Ω : Type*} (Q : ℕ) (request : S → ℕ) (update : S → Ω → S)
    (z : QueryBudgetState S) (hz : z.2.1 ≤ Q) (ω : Ω) :
    (queryBudgetStep Q request update z ω).2.1 ≤ Q := by
  unfold queryBudgetStep
  split_ifs with h h'
  · exact hz
  · exact h'
  · exact hz

/-- The finite budget is enforced on every sample path, including paths
where any local statistical estimate fails. -/
theorem queryBudgetRun_spent_le {S Ω : Type*} (Q : ℕ) (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) (n : ℕ) (w : Draws Ω n) :
    (queryBudgetRun Q initial request update n w).2.1 ≤ Q := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact queryBudgetStep_spent_le Q _ _ _ (ih w.1) w.2

/-- Exact coupling to the uncapped program. Nonnegative query costs make
the final uncapped cost control every earlier preflight request as well. -/
theorem queryBudgetRun_dichotomy {S Ω : Type*} (Q : ℕ) (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) (n : ℕ) (w : Draws Ω n) :
    (callCost initial request update n w ≤ Q ∧ queryBudgetRun Q initial request update n w =
      (callRun initial update n w,callCost initial request update n w,false)) ∨
    (Q < callCost initial request update n w ∧ (queryBudgetRun Q initial request update n w).2.2 = true) := by
  induction n with
  | zero => exact Or.inl ⟨Nat.zero_le _,rfl⟩
  | succ n ih =>
    rcases ih w.1 with ⟨hc,he⟩ | ⟨hc,he⟩
    · by_cases hn : callCost initial request update (n+1) w ≤ Q
      · left
        refine ⟨hn, ?_⟩
        rw [queryBudgetRun, he]
        simpa only [queryBudgetStep, Bool.false_eq_true, ↓reduceIte, callRun, callCost,
          freshHistoryCost] using
          (if_pos hn : (if callCost initial request update (n+1) w ≤ Q then
            (callRun initial update (n+1) w,callCost initial request update (n+1) w,false)
            else (callRun initial update n w.1,callCost initial request update n w.1,true)) = _)
      · right
        refine ⟨Nat.lt_of_not_le hn, ?_⟩
        rw [queryBudgetRun, he]
        have hn' : ¬callCost initial request update n w.1+
            request n (callRun initial update n w.1) ≤ Q := hn
        simp [queryBudgetStep, hn']
    · right
      refine ⟨?_, ?_⟩
      · change Q < callCost initial request update n w.1+request n (callRun initial update n w.1)
        omega
      · rw [queryBudgetRun, queryBudgetStep_frozen _ _ _ _ he]
        exact he

theorem queryBudgetRun_rejected_iff {S Ω : Type*} (Q : ℕ) (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) (n : ℕ) (w : Draws Ω n) :
    (queryBudgetRun Q initial request update n w).2.2 = true ↔ Q < callCost initial request update n w := by
  rcases queryBudgetRun_dichotomy Q initial request update n w with ⟨hc,he⟩ | ⟨hc,he⟩
  · simp [he, Nat.not_lt.mpr hc]
  · simp [he,hc]

theorem queryBudgetRun_agrees {S Ω : Type*} (Q : ℕ) (initial : S) (request : ℕ → S → ℕ)
    (update : ℕ → S → Ω → S) (n : ℕ) (w : Draws Ω n) (hc : callCost initial request update n w ≤ Q) :
    queryBudgetRun Q initial request update n w =
      (callRun initial update n w,callCost initial request update n w,false) := by
  rcases queryBudgetRun_dichotomy Q initial request update n w with ⟨_,he⟩ | ⟨hn,_⟩
  · exact he
  · omega

end
end SecondOrder
