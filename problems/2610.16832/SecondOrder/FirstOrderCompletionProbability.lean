import SecondOrder.FirstOrderStageCompletion

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderStageReached_fast_probability (P : FirstOrderPolicy d T S)
    (hd : 0<d) (A β R : ℝ) (hR : 2≤R) (i : Fin (T+1)) (hi : 0 < i.val) (cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (firstOrderStageReached P w.1 A β (finiteHistoryTape a₀ N w.2) i N ∧
        firstOrderStageResponseCount P w.1 A β (finiteHistoryTape a₀ N w.2) i.val N<cap))≤1/32 := by
  apply le_trans _ (firstOrderStageFast_probability P hd A β R hR i cap dummy a₀ N hhorizon hlarge hcap)
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  apply pmfMean_mono
  intro w
  have hh := firstOrderStageReached_fast P w.1 A β (finiteHistoryTape a₀ N w.2) i hi cap N
  split_ifs <;> norm_num <;> tauto

/-- A budget below half the full positive-stage cost completes the actual
comparison chain with probability at most 1/16. All fast-stage and charging
premises are now proved for the concrete recursive algorithm. -/
theorem firstOrderComparison_completion_probability (P : FirstOrderPolicy d T S)
    (hd : 0<d) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ N)
      (fun w => decide (firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ N w.2) N=T+1))≤1/16 := by
  apply sequential_completion_probability (firstOrderComparisonJointLaw P A β R hR a₀ N) hT hcap0
    (fun i : Fin T => fun w => firstOrderStageResponseCount P w.1 A β (finiteHistoryTape a₀ N w.2) (i.val+1) N)
    (fun i : Fin T => fun w => decide (firstOrderStageReached P w.1 A β (finiteHistoryTape a₀ N w.2) i.succ N))
    (fun w => decide (firstOrderComparisonOutputProgress P w.1 A β (finiteHistoryTape a₀ N w.2) N=T+1))
  · intro w hc i
    simp only [decide_eq_true_eq] at hc ⊢
    exact firstOrderComparison_complete_reached P w.1 A β (finiteHistoryTape a₀ N w.2) N hc i.succ
  · intro w
    exact firstOrderStageResponseCount_budget P w.1 A β (finiteHistoryTape a₀ N w.2) N
  · exact hbudget
  · intro i
    simpa only [decide_eq_true_eq, Fin.val_succ] using
      firstOrderStageReached_fast_probability P hd A β R hR i.succ (by simp) cap dummy a₀ N hhorizon hlarge hcap

end
end SecondOrder
