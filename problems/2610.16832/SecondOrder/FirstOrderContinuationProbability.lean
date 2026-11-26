import SecondOrder.FirstOrderCappedStageLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderContinuationTrueLaw (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) (n : ℕ) :=
  firstOrderCappedTrueLaw Θ R hR i (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀) cap n

/-- The actual query/output map of the capped continuation, read from its
finite coefficient history. No hidden target vector is used in this map. -/
def firstOrderContinuationQuery (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (t : Fin (n+1))
    (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) : Point d :=
  firstOrderDilation d T β (P.query (start+t.val)
    (stateTapeRun (0,s₀) (firstOrderContinuationStep P Θ A β start i.val cap dummy)
      (finiteHistoryTape a₀ n h) t.val).2) i

/-- Instantiation of the information bound for the concrete capped policy
continuation from any fixed entry state and time. The final output is included. -/
theorem firstOrderContinuation_activation_probability (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))))) :
    pmfEventProbability (firstOrderContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤
      (firstOrderArrayInformation d R*cap+Real.log 2)/B :=
  firstOrderCappedStage_activation_probability Θ R hR i _
    (firstOrderContinuationIndex_le P Θ A β start i.val cap dummy s₀) cap n
    (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n) hB hrare hlog

theorem firstOrderContinuation_activation_one_thirty_second (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)))))
    (hbudget : 32*(firstOrderArrayInformation d R*cap+Real.log 2)≤B) :
    pmfEventProbability (firstOrderContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 :=
  firstOrderCappedStage_activation_one_thirty_second Θ R hR i _
    (firstOrderContinuationIndex_le P Θ A β start i.val cap dummy s₀) cap n
    (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n) hB hrare hlog hbudget

end
end SecondOrder
