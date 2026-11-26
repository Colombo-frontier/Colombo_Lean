import SecondOrder.FirstOrderSuccessProbability
import SecondOrder.FiniteStateTape

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Continue from a fixed entry state, examining only blocks strictly before
the target. After the response cap, the policy receives a fixed dummy reply. -/
def firstOrderContinuationStep (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    {R : ℝ} (n : ℕ) (s : ℕ × S) (z : FirstOrderCoefficients d T R) : ℕ × S :=
  let x := P.query (start+n) s.2
  let k := firstOrderLimitedProgress Θ β x stage
  if s.1<cap then (s.1+(if k=stage then 1 else 0),P.update (start+n) s.2 (scaledFirstOrderTruncatedReply Θ A β z k x))
  else (s.1,P.update (start+n) s.2 dummy)

def firstOrderContinuationIndex (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S)
    {R : ℝ} (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) : ℕ :=
  firstOrderLimitedProgress Θ β (P.query (start+n)
    (finiteStateRun (0,s₀) (firstOrderContinuationStep P Θ A β start stage cap dummy) n h).2) stage

theorem firstOrderContinuationIndex_le (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S)
    {R : ℝ} (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    firstOrderContinuationIndex P Θ A β start stage cap dummy s₀ n h≤stage :=
  (firstOrderLimitedProgress_le Θ β _ stage).2

theorem firstOrderContinuationStep_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) {R : ℝ} (n : ℕ) (s : ℕ × S)
    (z : FirstOrderCoefficients d T R) (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    firstOrderContinuationStep P Θ A β start stage cap dummy n s z=
      firstOrderContinuationStep P Θ' A β start stage cap dummy n s z := by
  have hk := firstOrderLimitedProgress_prefix Θ Θ' β (P.query (start+n) s.2) stage hΘ
  have hr := scaledFirstOrderTruncatedReply_hidden_prefix Θ Θ' A β z
    (firstOrderLimitedProgress Θ β (P.query (start+n) s.2) stage)
    (fun i hi => hΘ i (lt_of_lt_of_le hi (firstOrderLimitedProgress_le Θ β _ stage).2))
    (P.query (start+n) s.2)
  unfold firstOrderContinuationStep
  dsimp only
  by_cases hc : s.1<cap
  · rw [if_pos hc, if_pos hc, hr, hk]
  · rw [if_neg hc, if_neg hc]

theorem firstOrderContinuationStep_count (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) {R : ℝ} (n : ℕ) (s : ℕ × S)
    (z : FirstOrderCoefficients d T R) :
    (firstOrderContinuationStep P Θ A β start stage cap dummy n s z).1=
      s.1+(if s.1<cap ∧ firstOrderLimitedProgress Θ β (P.query (start+n) s.2) stage=stage then 1 else 0) := by
  unfold firstOrderContinuationStep
  split_ifs <;> simp_all

theorem firstOrderContinuation_count (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ} :
    ∀ n (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n),
    (finiteStateRun (0,s₀) (firstOrderContinuationStep P Θ A β start stage cap dummy) n h).1=
      cappedHistoryCount (firstOrderStageSelected (firstOrderContinuationIndex P Θ A β start stage cap dummy s₀) stage) cap n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [finiteStateRun, firstOrderContinuationStep_count, cappedHistoryCount, ←ih h.1]
    simp only [firstOrderStageSelected, firstOrderContinuationIndex, decide_eq_true_eq]

theorem firstOrderContinuation_count_le (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ}
    (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :
    (finiteStateRun (0,s₀) (firstOrderContinuationStep P Θ A β start stage cap dummy) n h).1≤cap := by
  rw [firstOrderContinuation_count]
  exact cappedHistoryCount_le _ cap n h

end
end SecondOrder
