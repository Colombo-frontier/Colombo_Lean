import SecondOrder.CurvatureCappedStageLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureContinuationTrueLaw (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) (n : ℕ) :=
  curvatureCappedTrueLaw Θ R hR i (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀) cap n

/-- The actual query/output map of the capped continuation, read from its
finite coefficient history. No hidden target vector is used in this map. -/
def curvatureContinuationQuery (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (start : ℕ) (i : Fin (T+1)) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (t : Fin (n+1))
    (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) : Point (2*m) :=
  curvatureDilation m T β (P.query (start+t.val)
    (stateTapeRun (0,s₀) (curvatureContinuationStep P Θ A β start i.val cap dummy)
      (finiteHistoryTape a₀ n h) t.val).2) i

/-- Instantiation of the information bound for the concrete capped policy
continuation from any fixed entry state and time. The final output is included. -/
theorem curvatureContinuation_activation_probability (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (n : ℕ) {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))))) :
    pmfEventProbability (curvatureContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤
      (curvatureArrayInformation m R*cap+Real.log 2)/B :=
  curvatureCappedStage_activation_probability Θ R hR i _
    (curvatureContinuationIndex_le P Θ A β start i.val cap dummy s₀) cap n
    (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n) hB hrare hlog

theorem curvatureContinuation_activation_one_thirty_second (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (start : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (n : ℕ) {B : ℝ} (hB : 0<B)
    (hrare : (n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512))<1)
    (hlog : B≤Real.log (1/((n+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512)))))
    (hbudget : 32*(curvatureArrayInformation m R*cap+Real.log 2)≤B) :
    pmfEventProbability (curvatureContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h))))≤1/32 :=
  curvatureCappedStage_activation_one_thirty_second Θ R hR i _
    (curvatureContinuationIndex_le P Θ A β start i.val cap dummy s₀) cap n
    (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n) hB hrare hlog hbudget

end
end SecondOrder
