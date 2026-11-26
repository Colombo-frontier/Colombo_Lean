import SecondOrder.CurvatureRestartBound

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

theorem curvatureStageEntry_conditional_probability (μ : PMF (BalancedVector m)) (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (i : Fin (T+1)) (n k : ℕ)
    (F : BalancedVector m → FiniteHistory Unit (CurvatureCoefficients m T R) (n+k) → Prop)
    {q : ℝ} (hfuture : ∀ h, curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n →
      pmfMean μ (fun θ => pmfEventProbability
        (curvatureRestartSamplingLaw P (Function.update Θ i θ) A β R hR n
          (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
          (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k)
        (fun u => decide (F θ (finiteHistoryAppend n h k u))))≤q) :
    pmfEventProbability (curvatureCoordinateSamplingLaw μ P Θ A β R hR a₀ i (n+k))
      (fun w => decide (curvatureStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n (finiteHistoryPrefix n k w.2)) i.val n ∧ F w.1 w.2))≤
      q*pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
        (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n)) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq, ite_and]
  rw [curvatureStageEntry_conditional_mean μ P Θ A β R hR a₀ i n k (fun θ h => if F θ h then 1 else 0),
    pmfEventProbability_mean, ←pmfMean_mul]
  apply pmfMean_mono
  intro h
  by_cases he : curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n
  · simp only [if_pos he, decide_eq_true_eq, mul_one]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hfuture h he
  · simp only [if_neg he, decide_eq_true_eq, mul_zero, le_refl]

/-- The future fast event uses the state actually reached by its own entry
prefix, and the actual suffix of the same sampled history. -/
def curvatureEntryFutureFast (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (i : Fin (T+1)) (cap : ℕ) {R : ℝ} (a₀ : CurvatureCoefficients m T R)
    (n k : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) (n+k)) : Prop :=
  let s := curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n (finiteHistoryPrefix n k h)) n
  curvatureRestartFastEvent P Θ A β n s.1 i cap s.2 a₀ k (finiteHistorySuffix n k h)

/-- The actual entry slice has fast probability at most 1/32 times its entry
probability. The entrance history is random and can be arbitrarily adaptive. -/
theorem curvatureStageEntry_fast_probability (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (a₀ : CurvatureCoefficients m T R) (n k : ℕ)
    (hhorizon : 1024*Real.log (4*(k+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m))
      P Θ A β R hR a₀ i (n+k))
      (fun w => decide (curvatureStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n (finiteHistoryPrefix n k w.2)) i.val n ∧
        curvatureEntryFutureFast P (Function.update Θ i w.1) A β i cap a₀ n k w.2))≤
      (1/32)*pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
        (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n)) := by
  apply curvatureStageEntry_conditional_probability (PMF.uniformOfFintype (BalancedVector m))
    P Θ A β R hR a₀ i n k (fun θ h => curvatureEntryFutureFast P (Function.update Θ i θ) A β i cap a₀ n k h)
  intro h he
  have hs (θ : BalancedVector m) :
      curvatureComparisonRun P (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) n=
        curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n := by
    symm
    apply (curvatureStageEntry_prefix P Θ (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) i.val n _ he).2
    intro j hj
    have hne : j≠i := by intro hh; subst j; omega
    simp only [Function.update_of_ne hne]
  simp only [curvatureEntryFutureFast, finiteHistoryPrefix_append, finiteHistorySuffix_append, hs]
  exact curvatureRestart_fast_one_thirty_second P Θ hm A β R hR n
    (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1 i cap dummy
    (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 a₀
    (Or.inl (curvatureStageEntry_progress P Θ A β _ he).1) k hhorizon hlarge hcap

end
end SecondOrder
