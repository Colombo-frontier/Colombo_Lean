import SecondOrder.CurvatureStageCompletion

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureStageReached_fast_probability (P : CurvaturePolicy m T S)
    (hm : 0<m) (A β R : ℝ) (hR : 2≤R) (i : Fin (T+1)) (hi : 0 < i.val) (cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (curvatureStageReached P w.1 A β (finiteHistoryTape a₀ N w.2) i N ∧
        curvatureStageResponseCount P w.1 A β (finiteHistoryTape a₀ N w.2) i.val N<cap))≤1/32 := by
  apply le_trans _ (curvatureStageFast_probability P hm A β R hR i cap dummy a₀ N hhorizon hlarge hcap)
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  apply pmfMean_mono
  intro w
  have hh := curvatureStageReached_fast P w.1 A β (finiteHistoryTape a₀ N w.2) i hi cap N
  split_ifs <;> norm_num <;> tauto

/-- A budget below half the full positive-stage cost completes the actual
comparison chain with probability at most 1/16. All fast-stage and charging
premises are now proved for the concrete recursive algorithm. -/
theorem curvatureComparison_completion_probability (P : CurvaturePolicy m T S)
    (hm : 0<m) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ N w.2) N=T+1))≤1/16 := by
  apply sequential_completion_probability (curvatureComparisonJointLaw P A β R hR a₀ N) hT hcap0
    (fun i : Fin T => fun w => curvatureStageResponseCount P w.1 A β (finiteHistoryTape a₀ N w.2) (i.val+1) N)
    (fun i : Fin T => fun w => decide (curvatureStageReached P w.1 A β (finiteHistoryTape a₀ N w.2) i.succ N))
    (fun w => decide (curvatureComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ N w.2) N=T+1))
  · intro w hc i
    simp only [decide_eq_true_eq] at hc ⊢
    exact curvatureComparison_complete_reached P w.1 A β (finiteHistoryTape a₀ N w.2) N hc i.succ
  · intro w
    exact curvatureStageResponseCount_budget P w.1 A β (finiteHistoryTape a₀ N w.2) N
  · exact hbudget
  · intro i
    simpa only [decide_eq_true_eq, Fin.val_succ] using
      curvatureStageReached_fast_probability P hm A β R hR i.succ (by simp) cap dummy a₀ N hhorizon hlarge hcap

end
end SecondOrder
