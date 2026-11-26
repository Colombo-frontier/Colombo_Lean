import SecondOrder.FiniteStateRestart

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureRestartSamplingLaw (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (start p : ℕ) (s₀ : S) (k : ℕ) :=
  finiteStateSamplingLaw (p,s₀) (fun t => curvatureComparisonStep P Θ A β (start+t))
    (fun t s => curvaturePrefixCoefficientLaw Θ R hR
      (curvatureLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)+1)) k

/-- Conditioning on a concrete finite prefix restarts the actual comparison
sampling from exactly the state and progress reached by that prefix. -/
theorem curvatureComparison_continuation_law (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (k : ℕ) :
    finiteContinuationLaw (curvatureComparisonTransition P Θ A β R hR a₀) n h k=
      curvatureRestartSamplingLaw P Θ A β R hR n
        (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k := by
  have he : finiteContinuationTransition (curvatureComparisonTransition P Θ A β R hR a₀) n h=
      finiteStateTransition
        ((curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1,
          (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2)
        (fun t => curvatureComparisonStep P Θ A β (n+t))
        (fun t s => curvaturePrefixCoefficientLaw Θ R hR
          (curvatureLimitedProgress Θ β (P.query (n+t) s.2) (s.1+1)+1)) := by
    funext t u
    unfold finiteContinuationTransition curvatureComparisonTransition
    rw [curvatureComparisonIndex_append]
    unfold finiteStateTransition curvatureRestartIndex curvatureRestartRun
    rw [finiteStateRun_eq_tape _ _ a₀ t u]
  unfold finiteContinuationLaw curvatureRestartSamplingLaw finiteStateSamplingLaw
  rw [he]

theorem curvatureComparison_append_mass (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (k : ℕ) (u : FiniteHistory Unit (CurvatureCoefficients m T R) k) :
    curvatureComparisonSamplingLaw P Θ A β R hR a₀ (n+k) (finiteHistoryAppend n h k u)=
      curvatureComparisonSamplingLaw P Θ A β R hR a₀ n h *
        curvatureRestartSamplingLaw P Θ A β R hR n
          (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
          (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k u := by
  have hh := finiteAdaptiveLaw_append_mass (PMF.pure ()) (curvatureComparisonTransition P Θ A β R hR a₀) n h k u
  rw [curvatureComparison_continuation_law] at hh
  exact hh

end
end SecondOrder
