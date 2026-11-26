import SecondOrder.FiniteSeedProbability
import SecondOrder.FirstOrderSeededQueryPolicy

open MeasureTheory
open scoped Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {d T : ℕ}

def firstOrderSeededSuccessProbability (μ : Measure Ξ) (P : Ξ → FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (success : (Fin (T+1) → (Fin d → Bool)) → Point (FirstOrderDimension d T) → Prop)
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ) : ℝ :=
  (μ.prod (firstOrderOriginalSamplingLaw Θ R hR N).toMeasure).real
    {w : Ξ × FiniteHistory Unit (FirstOrderCoefficients d T R) N |
      success Θ (firstOrderOriginalOutput (P w.1) Θ A β a₀ N w.2)}

theorem firstOrderSeeded_success_integral (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (hP : MeasurableQueryPolicyFamily P)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (success : (Fin (T+1) → (Fin d → Bool)) → Point (FirstOrderDimension d T) → Prop)
    (hsuccess : ∀ Θ, MeasurableSet {x | success Θ x}) (a₀ : FirstOrderCoefficients d T R) (N : ℕ) :
    firstOrderSeededSuccessProbability μ P Θ A β R hR success a₀ N=
      ∫ ξ, pmfEventProbability (firstOrderOriginalSamplingLaw Θ R hR N)
        (fun h => decide (success Θ (firstOrderOriginalOutput (P ξ) Θ A β a₀ N h))) ∂μ :=
  finiteSeed_probability_eq_integral μ (firstOrderOriginalSamplingLaw Θ R hR N) _
    (fun h => (hsuccess Θ).preimage (firstOrderOriginalOutput_measurable_seed P hP Θ A β a₀ N h))

theorem firstOrderSeeded_success_one_eighth (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (hP : MeasurableQueryPolicyFamily P)
    (hd : 0<d) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ))
    (success : (Fin (T+1) → (Fin d → Bool)) → Point (FirstOrderDimension d T) → Prop)
    (hsuccess : ∀ Θ, MeasurableSet {x | success Θ x})
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x)=T+1) :
    pmfMean (firstOrderHiddenPrior d T)
      (fun Θ => firstOrderSeededSuccessProbability μ P Θ A β R hR success a₀ N)≤1/8 := by
  simp_rw [firstOrderSeeded_success_integral μ P hP _ _ _ _ _ success hsuccess]
  apply finiteSeed_hidden_mean_le μ (firstOrderHiddenPrior d T)
    (fun Θ => firstOrderOriginalSamplingLaw Θ R hR N)
    (fun ξ Θ h => success Θ (firstOrderOriginalOutput (P ξ) Θ A β a₀ N h))
    (fun Θ h => (hsuccess Θ).preimage (firstOrderOriginalOutput_measurable_seed P hP Θ A β a₀ N h))
  intro ξ
  have hh := firstOrderOriginal_success_one_eighth (P ξ) hd hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar success hcomplete
  simpa only [pmfEventProbability_mean, firstOrderOriginalJointLaw, finiteConditionalPMF_mean] using hh

end
end SecondOrder
