import SecondOrder.FiniteStateTape

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Continue from a fixed entry state, examining only blocks strictly before
the target. After the response cap, the policy receives a fixed dummy reply. -/
def curvatureContinuationStep (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    {R : ℝ} (n : ℕ) (s : ℕ × S) (z : CurvatureCoefficients m T R) : ℕ × S :=
  let x := P.query (start+n) s.2
  let k := curvatureLimitedProgress Θ β x stage
  if s.1<cap then (s.1+(if k=stage then 1 else 0),P.update (start+n) s.2 (scaledCurvatureTruncatedReply Θ A β z k x))
  else (s.1,P.update (start+n) s.2 dummy)

def curvatureContinuationIndex (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (CurvatureDimension m T)) (s₀ : S)
    {R : ℝ} (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) : ℕ :=
  curvatureLimitedProgress Θ β (P.query (start+n)
    (finiteStateRun (0,s₀) (curvatureContinuationStep P Θ A β start stage cap dummy) n h).2) stage

theorem curvatureContinuationIndex_le (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start stage cap : ℕ) (dummy : RichReply (CurvatureDimension m T)) (s₀ : S)
    {R : ℝ} (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) :
    curvatureContinuationIndex P Θ A β start stage cap dummy s₀ n h≤stage :=
  (curvatureLimitedProgress_le Θ β _ stage).2

theorem curvatureContinuationStep_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) {R : ℝ} (n : ℕ) (s : ℕ × S)
    (z : CurvatureCoefficients m T R) (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    curvatureContinuationStep P Θ A β start stage cap dummy n s z=
      curvatureContinuationStep P Θ' A β start stage cap dummy n s z := by
  have hk := curvatureLimitedProgress_prefix Θ Θ' β (P.query (start+n) s.2) stage hΘ
  have hr := scaledCurvatureTruncatedReply_hidden_prefix Θ Θ' A β z
    (curvatureLimitedProgress Θ β (P.query (start+n) s.2) stage)
    (fun i hi => hΘ i (lt_of_lt_of_le hi (curvatureLimitedProgress_le Θ β _ stage).2))
    (P.query (start+n) s.2)
  unfold curvatureContinuationStep
  dsimp only
  by_cases hc : s.1<cap
  · rw [if_pos hc, if_pos hc, hr, hk]
  · rw [if_neg hc, if_neg hc]

theorem curvatureContinuationStep_count (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) {R : ℝ} (n : ℕ) (s : ℕ × S)
    (z : CurvatureCoefficients m T R) :
    (curvatureContinuationStep P Θ A β start stage cap dummy n s z).1=
      s.1+(if s.1<cap ∧ curvatureLimitedProgress Θ β (P.query (start+n) s.2) stage=stage then 1 else 0) := by
  unfold curvatureContinuationStep
  split_ifs <;> simp_all

theorem curvatureContinuation_count (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) {R : ℝ} :
    ∀ n (h : FiniteHistory Unit (CurvatureCoefficients m T R) n),
    (finiteStateRun (0,s₀) (curvatureContinuationStep P Θ A β start stage cap dummy) n h).1=
      cappedHistoryCount (curvatureStageSelected (curvatureContinuationIndex P Θ A β start stage cap dummy s₀) stage) cap n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [finiteStateRun, curvatureContinuationStep_count, cappedHistoryCount, ←ih h.1]
    simp only [curvatureStageSelected, curvatureContinuationIndex, decide_eq_true_eq]

theorem curvatureContinuation_count_le (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) (start stage cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) {R : ℝ}
    (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) :
    (finiteStateRun (0,s₀) (curvatureContinuationStep P Θ A β start stage cap dummy) n h).1≤cap := by
  rw [curvatureContinuation_count]
  exact cappedHistoryCount_le _ cap n h

end
end SecondOrder
