import SecondOrder.FirstOrderCompletionProbability

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- The concrete sequential lower bound for any deterministic adaptive policy
using full value/gradient/Hessian replies from the original fresh-sample law. -/
theorem firstOrderOriginal_success_one_eighth (P : FirstOrderPolicy d T S)
    (hd : 0<d) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ))
    (success : (Fin (T+1) → (Fin d → Bool)) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x)=T+1) :
    pmfEventProbability (firstOrderOriginalJointLaw d T R hR N)
      (fun w => decide (success w.1 (firstOrderOriginalOutput P w.1 A β a₀ N w.2)))≤1/8 := by
  have hs := firstOrderOriginal_success_probability P A β R hR a₀ N success hcomplete
  have hc := firstOrderComparison_completion_probability P hd hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap
  have hf := firstOrderFarHorizon_small N T hfar
  linarith only [hs,hc,hf]

/-- The original scalar-loss oracle cannot return a small gradient with high
probability under the explicit stage and horizon budgets. -/
theorem firstOrderOriginal_gradient_one_eighth (P : FirstOrderPolicy d T S)
    (hd : 0<d) (hT : 0<T) {A β ε : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ)) :
    pmfEventProbability (firstOrderOriginalJointLaw d T R hR N)
      (fun w => decide (‖gradient (scaledFirstOrderPopulation w.1 A β)
        (firstOrderOriginalOutput P w.1 A β a₀ N w.2)‖≤ε))≤1/8 :=
  firstOrderOriginal_success_one_eighth P hd hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar _
    (fun Θ _ hx => scaledFirstOrderPopulation_gradient_progress Θ hd hA hβ hε hx)

/-- Averaging over the finite hidden prior selects one hard objective for
each deterministic policy. Private-seed integration is a separate step. -/
theorem firstOrderOriginal_exists_hard_target (P : FirstOrderPolicy d T S)
    (hd : 0<d) (hT : 0<T) {A β ε : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ)) :
    ∃ Θ : Fin (T+1) → Fin d → Bool,
      pmfEventProbability (firstOrderOriginalSamplingLaw Θ R hR N)
        (fun h => decide (‖gradient (scaledFirstOrderPopulation Θ A β)
          (firstOrderOriginalOutput P Θ A β a₀ N h)‖≤ε))<1/4 := by
  have hh := firstOrderOriginal_gradient_one_eighth P hd hT hA hβ hε R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  simp only [pmfEventProbability_mean,firstOrderOriginalJointLaw,finiteConditionalPMF_mean] at hh ⊢
  apply exists_below_pmfMean_bound (firstOrderHiddenPrior d T)
  linarith only [hh]

end
end SecondOrder

