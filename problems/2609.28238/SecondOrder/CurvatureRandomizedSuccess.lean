import SecondOrder.CurvatureEndpointSmallness

open MeasureTheory
open scoped Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {m T : ℕ}

def curvatureSeededSuccessProbability (μ : Measure Ξ) (P : Ξ → CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (success : (Fin (T+1) → BalancedVector m) → Point (CurvatureDimension m T) → Prop)
    (a₀ : CurvatureCoefficients m T R) (N : ℕ) : ℝ :=
  (μ.prod (curvatureOriginalSamplingLaw Θ R hR N).toMeasure).real
    {w : Ξ × FiniteHistory Unit (CurvatureCoefficients m T R) N |
      success Θ (curvatureOriginalOutput (P w.1) Θ A β a₀ N w.2)}

theorem curvatureSeeded_success_integral (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (hP : MeasurableQueryPolicyFamily P)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (success : (Fin (T+1) → BalancedVector m) → Point (CurvatureDimension m T) → Prop)
    (hsuccess : ∀ Θ, MeasurableSet {x | success Θ x}) (a₀ : CurvatureCoefficients m T R) (N : ℕ) :
    curvatureSeededSuccessProbability μ P Θ A β R hR success a₀ N=
      ∫ ξ, pmfEventProbability (curvatureOriginalSamplingLaw Θ R hR N)
        (fun h => decide (success Θ (curvatureOriginalOutput (P ξ) Θ A β a₀ N h))) ∂μ :=
  finiteSeed_probability_eq_integral μ (curvatureOriginalSamplingLaw Θ R hR N) _
    (fun h => (hsuccess Θ).preimage (curvatureOriginalOutput_measurable_seed P hP Θ A β a₀ N h))

theorem curvatureSeeded_success_one_eighth (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (hP : MeasurableQueryPolicyFamily P)
    (hm : 0<m) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ))
    (success : (Fin (T+1) → BalancedVector m) → Point (CurvatureDimension m T) → Prop)
    (hsuccess : ∀ Θ, MeasurableSet {x | success Θ x})
    (hcomplete : ∀ Θ x, success Θ x → curvatureProgress Θ (curvatureDilation m T β x)=T+1) :
    pmfMean (curvatureHiddenPrior m T)
      (fun Θ => curvatureSeededSuccessProbability μ P Θ A β R hR success a₀ N)≤1/8 := by
  simp_rw [curvatureSeeded_success_integral μ P hP _ _ _ _ _ success hsuccess]
  apply finiteSeed_hidden_mean_le μ (curvatureHiddenPrior m T)
    (fun Θ => curvatureOriginalSamplingLaw Θ R hR N)
    (fun ξ Θ h => success Θ (curvatureOriginalOutput (P ξ) Θ A β a₀ N h))
    (fun Θ h => (hsuccess Θ).preimage (curvatureOriginalOutput_measurable_seed P hP Θ A β a₀ N h))
  intro ξ
  have hh := curvatureOriginal_success_one_eighth (P ξ) hm hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar success hcomplete
  simpa only [pmfEventProbability_mean, curvatureOriginalJointLaw, finiteConditionalPMF_mean] using hh

def HasSecondOrderCertificate {d : ℕ} (F : Point d → ℝ) (γ : ℝ) (x : Point d) : Prop :=
  ∀ v : Point d, -γ*‖v‖^2≤⟪hessian F x v,v⟫_ℝ

theorem hasSecondOrderCertificate_measurableSet {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) (γ : ℝ) : MeasurableSet {x | HasSecondOrderCertificate F γ x} :=
  (rayleighCertificate_closed γ).measurableSet.preimage (continuous_hessian hF).measurable

theorem curvatureHardFamily_secondOrder_progress (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {L γ : ℝ} (hL : 0<L) (hγ : 0<γ) {x : Point (CurvatureDimension m T)}
    (hx : HasSecondOrderCertificate
      (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ)) γ x) :
    curvatureProgress Θ (curvatureDilation m T (curvatureInputScale L γ) x)=T+1 :=
  curvatureHardFamily_sosp_progress Θ hm hL hγ ⟨le_refl _,hx⟩

end
end SecondOrder
