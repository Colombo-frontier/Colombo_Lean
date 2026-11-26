import SecondOrder.FirstOrderRestartBound

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderStageEntry_conditional_probability (μ : PMF ((Fin d → Bool))) (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (i : Fin (T+1)) (n k : ℕ)
    (F : (Fin d → Bool) → FiniteHistory Unit (FirstOrderCoefficients d T R) (n+k) → Prop)
    {q : ℝ} (hfuture : ∀ h, firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n →
      pmfMean μ (fun θ => pmfEventProbability
        (firstOrderRestartSamplingLaw P (Function.update Θ i θ) A β R hR n
          (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
          (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 k)
        (fun u => decide (F θ (finiteHistoryAppend n h k u))))≤q) :
    pmfEventProbability (firstOrderCoordinateSamplingLaw μ P Θ A β R hR a₀ i (n+k))
      (fun w => decide (firstOrderStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n (finiteHistoryPrefix n k w.2)) i.val n ∧ F w.1 w.2))≤
      q*pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
        (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n)) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq, ite_and]
  rw [firstOrderStageEntry_conditional_mean μ P Θ A β R hR a₀ i n k (fun θ h => if F θ h then 1 else 0),
    pmfEventProbability_mean, ←pmfMean_mul]
  apply pmfMean_mono
  intro h
  by_cases he : firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n
  · simp only [if_pos he, decide_eq_true_eq, mul_one]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hfuture h he
  · simp only [if_neg he, decide_eq_true_eq, mul_zero, le_refl]

/-- The future fast event uses the state actually reached by its own entry
prefix, and the actual suffix of the same sampled history. -/
def firstOrderEntryFutureFast (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) (i : Fin (T+1)) (cap : ℕ) {R : ℝ} (a₀ : FirstOrderCoefficients d T R)
    (n k : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) (n+k)) : Prop :=
  let s := firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n (finiteHistoryPrefix n k h)) n
  firstOrderRestartFastEvent P Θ A β n s.1 i cap s.2 a₀ k (finiteHistorySuffix n k h)

/-- The actual entry slice has fast probability at most 1/32 times its entry
probability. The entrance history is random and can be arbitrarily adaptive. -/
theorem firstOrderStageEntry_fast_probability (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0<d) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (a₀ : FirstOrderCoefficients d T R) (n k : ℕ)
    (hhorizon : 256*Real.log (2*(k+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool)))
      P Θ A β R hR a₀ i (n+k))
      (fun w => decide (firstOrderStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n (finiteHistoryPrefix n k w.2)) i.val n ∧
        firstOrderEntryFutureFast P (Function.update Θ i w.1) A β i cap a₀ n k w.2))≤
      (1/32)*pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
        (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n)) := by
  apply firstOrderStageEntry_conditional_probability (PMF.uniformOfFintype ((Fin d → Bool)))
    P Θ A β R hR a₀ i n k (fun θ h => firstOrderEntryFutureFast P (Function.update Θ i θ) A β i cap a₀ n k h)
  intro h he
  have hs (θ : (Fin d → Bool)) :
      firstOrderComparisonRun P (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) n=
        firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n := by
    symm
    apply (firstOrderStageEntry_prefix P Θ (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) i.val n _ he).2
    intro j hj
    have hne : j≠i := by intro hh; subst j; omega
    simp only [Function.update_of_ne hne]
  simp only [firstOrderEntryFutureFast, finiteHistoryPrefix_append, finiteHistorySuffix_append, hs]
  exact firstOrderRestart_fast_one_thirty_second P Θ hd A β R hR n
    (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1 i cap dummy
    (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 a₀
    (Or.inl (firstOrderStageEntry_progress P Θ A β _ he).1) k hhorizon hlarge hcap

end
end SecondOrder

