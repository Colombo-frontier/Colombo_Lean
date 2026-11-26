import SecondOrder.CurvatureContinuationMixture

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Averaging the actual restarted algorithm over the hidden target is bounded
by the already analysed capped experiment, for any fixed entry state. -/
theorem curvatureRestart_fast_probability_le (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ) :
    pmfMean (PMF.uniformOfFintype (BalancedVector m)) (fun θ =>
      pmfEventProbability (curvatureRestartSamplingLaw P (Function.update Θ i θ) A β R hR start p s₀ n)
        (fun h => decide (curvatureRestartFastEvent P (Function.update Θ i θ) A β start p i cap s₀ a₀ n h)))≤
    pmfEventProbability (curvatureContinuationTrueLaw P Θ A β R hR start i cap dummy s₀ n)
      (fun h => decide (∃ t, 0<periodicCompletion (finiteHistoryInitial n h).1
        (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t (finiteHistoryMapInitial Prod.snd n h)))) := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  rw [curvatureContinuationTrueLaw_mean P Θ A β R hR start i cap dummy s₀ n
    (fun θ h => if ∃ t, 0<periodicCompletion θ
      (curvatureContinuationQuery P Θ A β start i cap dummy s₀ a₀ n t h) then 1 else 0)]
  apply pmfMean_mono
  intro θ
  simpa only [Function.update_self, curvatureContinuationQuery_update] using
    curvatureRestart_fast_le_activation P (Function.update Θ i θ) A β R hR start p i cap dummy s₀ a₀ hp n

/-- Explicit fast-stage bound for the genuine restarted sampling law. -/
theorem curvatureRestart_fast_one_thirty_second (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (hp : p+1=i.val ∨ p=i.val) (n : ℕ)
    (hhorizon : 1024*Real.log (4*(n+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfMean (PMF.uniformOfFintype (BalancedVector m)) (fun θ =>
      pmfEventProbability (curvatureRestartSamplingLaw P (Function.update Θ i θ) A β R hR start p s₀ n)
        (fun h => decide (curvatureRestartFastEvent P (Function.update Θ i θ) A β start p i cap s₀ a₀ n h)))≤1/32 :=
  le_trans (curvatureRestart_fast_probability_le P Θ A β R hR start p i cap dummy s₀ a₀ hp n)
    (curvatureContinuation_activation_explicit P Θ hm A β R hR start i cap dummy s₀ a₀ n hhorizon hlarge hcap)

end
end SecondOrder
