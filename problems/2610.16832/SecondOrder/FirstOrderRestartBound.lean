import SecondOrder.FirstOrderContinuationMixture

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Averaging the actual restarted algorithm over the hidden target is bounded
by the already analysed capped experiment, for any fixed entry state. -/
theorem firstOrderRestart_fast_probability_le (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ) :
    pmfMean (PMF.uniformOfFintype ((Fin d → Bool))) (fun θ =>
      pmfEventProbability (firstOrderRestartSamplingLaw P (Function.update Θ i θ) A β R hR start p s₀ n)
        (fun h => decide (firstOrderRestartFastEvent P (Function.update Θ i θ) A β start p i cap s₀ a₀ n h)))≤
    pmfEventProbability (firstOrderContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<firstOrderBlockCompletion (finiteHistoryInitial n h).1
        (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h)))) := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  rw [firstOrderContinuationTrueLaw_mean P Θ A β R hR start i cap dummy s₀ n
    (fun θ h => if ∃ t, 0<firstOrderBlockCompletion θ
      (firstOrderContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t h) then 1 else 0)]
  apply pmfMean_mono
  intro θ
  simpa only [Function.update_self, firstOrderContinuationQuery_update] using
    firstOrderRestart_fast_le_activation P (Function.update Θ i θ) A β R hR start p i cap dummy s₀ a₀ hp n

/-- Explicit fast-stage bound for the genuine restarted sampling law. -/
theorem firstOrderRestart_fast_one_thirty_second (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0<d) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ)
    (hhorizon : 256*Real.log (2*(n+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfMean (PMF.uniformOfFintype ((Fin d → Bool))) (fun θ =>
      pmfEventProbability (firstOrderRestartSamplingLaw P (Function.update Θ i θ) A β R hR start p s₀ n)
        (fun h => decide (firstOrderRestartFastEvent P (Function.update Θ i θ) A β start p i cap s₀ a₀ n h)))≤1/32 :=
  le_trans (firstOrderRestart_fast_probability_le P Θ A β R hR start p i cap dummy s₀ a₀ hp n)
    (firstOrderContinuation_activation_explicit P Θ hd A β R hR start i cap dummy s₀ a₀ n hhorizon hlarge hcap)

end
end SecondOrder
