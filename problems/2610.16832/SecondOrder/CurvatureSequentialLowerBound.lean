import SecondOrder.CurvatureCompletionProbability

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- The concrete sequential lower bound for any deterministic adaptive policy
using full value/gradient/Hessian replies from the original fresh-sample law. -/
theorem curvatureOriginal_success_one_eighth (P : CurvaturePolicy m T S)
    (hm : 0<m) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ))
    (success : (Fin (T+1) → BalancedVector m) → Point (CurvatureDimension m T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → curvatureProgress Θ (curvatureDilation m T β x)=T+1) :
    pmfEventProbability (curvatureOriginalJointLaw m T R hR N)
      (fun w => decide (success w.1 (curvatureOriginalOutput P w.1 A β a₀ N w.2)))≤1/8 := by
  have hs := curvatureOriginal_success_probability P A β R hR a₀ N success hcomplete
  have hc := curvatureComparison_completion_probability P hm hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap
  have hf := curvatureFarHorizon_small N T hfar
  linarith only [hs,hc,hf]

/-- The original common-random-loss SOSP event, with all stage and history
probability bounds instantiated. Numerical parameter choice and private-seed
integration are separate from this deterministic-policy statement. -/
theorem curvatureOriginal_sosp_one_eighth (P : CurvaturePolicy m T S)
    (hm : 0<m) (hT : 0<T) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ)) :
    pmfEventProbability (curvatureOriginalJointLaw m T R hR N)
      (fun w => decide (IsSOSP (scaledCurvaturePopulation w.1 (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
        (curvatureInputScale L γ)) ε γ
        (curvatureOriginalOutput P w.1 (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) a₀ N w.2)))≤1/8 :=
  curvatureOriginal_success_one_eighth P hm hT _ _ R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar _ (fun Θ _ hx => curvatureHardFamily_sosp_progress Θ hm hL hγ hx)

/-- A deterministic hidden family member defeats each fixed deterministic
policy. This does not yet quantify over an arbitrary private seed law. -/
theorem curvatureOriginal_exists_hard_target (P : CurvaturePolicy m T S)
    (hm : 0<m) (hT : 0<T) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ)) :
    ∃ Θ : Fin (T+1) → BalancedVector m,
      pmfEventProbability (curvatureOriginalSamplingLaw Θ R hR N)
        (fun h => decide (IsSOSP (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
          (curvatureInputScale L γ)) ε γ
          (curvatureOriginalOutput P Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) a₀ N h)))<1/4 := by
  have hh := curvatureOriginal_sosp_one_eighth P hm hT (ε := ε) hL hγ R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  simp only [pmfEventProbability_mean, curvatureOriginalJointLaw, finiteConditionalPMF_mean] at hh ⊢
  apply exists_below_pmfMean_bound (curvatureHiddenPrior m T)
  linarith only [hh]

end
end SecondOrder
