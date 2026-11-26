import SecondOrder.FirstOrderContinuationCoupling
import SecondOrder.FirstOrderStateRestart

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderRestartSamplingLaw (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (start p : ℕ) (s₀ : S) (k : ℕ) :=
  finiteStateSamplingLaw (p,s₀) (fun t => firstOrderComparisonStep P Θ A β (start+t))
    (fun t s => firstOrderPrefixCoefficientLaw Θ R hR
      (firstOrderLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)+1)) k

/-- Conditioning on a concrete finite prefix restarts the actual comparison
sampling from exactly the state and progress reached by that prefix. -/
theorem firstOrderComparison_continuation_law (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (k : ℕ) :
    finiteContinuationLaw (firstOrderComparisonTransition P Θ A β R hR a₀) n h k=
      firstOrderRestartSamplingLaw P Θ A β R hR n
        (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k := by
  have he : finiteContinuationTransition (firstOrderComparisonTransition P Θ A β R hR a₀) n h=
      finiteStateTransition
        ((firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1,
          (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2)
        (fun t => firstOrderComparisonStep P Θ A β (n+t))
        (fun t s => firstOrderPrefixCoefficientLaw Θ R hR
          (firstOrderLimitedProgress Θ β (P.query (n+t) s.2) (s.1+1)+1)) := by
    funext t u
    unfold finiteContinuationTransition firstOrderComparisonTransition
    rw [firstOrderComparisonIndex_append]
    unfold finiteStateTransition firstOrderRestartIndex firstOrderRestartRun
    rw [finiteStateRun_eq_tape _ _ a₀ t u]
  unfold finiteContinuationLaw firstOrderRestartSamplingLaw finiteStateSamplingLaw
  rw [he]

theorem firstOrderComparison_append_mass (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (k : ℕ) (u : FiniteHistory Unit (FirstOrderCoefficients d T R) k) :
    firstOrderComparisonSamplingLaw P Θ A β R hR a₀ (n+k) (finiteHistoryAppend n h k u)=
      firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n h *
        firstOrderRestartSamplingLaw P Θ A β R hR n
          (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
          (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k u := by
  have hh := finiteAdaptiveLaw_append_mass (PMF.pure ()) (firstOrderComparisonTransition P Θ A β R hR a₀) n h k u
  rw [firstOrderComparison_continuation_law] at hh
  exact hh

end
end SecondOrder

