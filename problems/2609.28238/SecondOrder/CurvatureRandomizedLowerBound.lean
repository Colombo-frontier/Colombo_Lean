import SecondOrder.FiniteSeedProbability

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {m T : ℕ}

/-- Success probability over the private seed and the original independent
fresh coefficient samples, for one fixed hidden instance. -/
def curvatureSeededSospProbability (μ : Measure Ξ) (P : Ξ → CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : CurvatureCoefficients m T R) (N : ℕ) : ℝ :=
  (μ.prod (curvatureOriginalSamplingLaw Θ R hR N).toMeasure).real
    {w : Ξ × FiniteHistory Unit (CurvatureCoefficients m T R) N |
      IsSOSP (scaledCurvaturePopulation Θ A β) ε γ (curvatureOriginalOutput (P w.1) Θ A β a₀ N w.2)}

theorem curvatureSeededSospProbability_integral (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (hP : MeasurableQueryPolicyFamily P)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : CurvatureCoefficients m T R) (N : ℕ) :
    curvatureSeededSospProbability μ P Θ A β R hR ε γ a₀ N=
      ∫ ξ, pmfEventProbability (curvatureOriginalSamplingLaw Θ R hR N)
        (fun h => decide (IsSOSP (scaledCurvaturePopulation Θ A β) ε γ
          (curvatureOriginalOutput (P ξ) Θ A β a₀ N h))) ∂μ :=
  finiteSeed_probability_eq_integral μ (curvatureOriginalSamplingLaw Θ R hR N) _
    (curvatureOriginal_sosp_measurable_seed P hP Θ A β ε γ a₀ N)

/-- The 1/8 average success bound for the entire randomized algorithm,
including an arbitrary private seed probability space. -/
theorem curvatureSeeded_sosp_one_eighth (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (hP : MeasurableQueryPolicyFamily P)
    (hm : 0<m) (hT : 0<T) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ)) :
    pmfMean (curvatureHiddenPrior m T) (fun Θ => curvatureSeededSospProbability μ P Θ
      (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) R hR ε γ a₀ N)≤1/8 := by
  simp_rw [curvatureSeededSospProbability_integral μ P hP]
  apply finiteSeed_hidden_mean_le μ (curvatureHiddenPrior m T)
    (fun Θ => curvatureOriginalSamplingLaw Θ R hR N)
    (fun ξ Θ h => IsSOSP (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ)) ε γ
      (curvatureOriginalOutput (P ξ) Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) a₀ N h))
    (fun Θ => curvatureOriginal_sosp_measurable_seed P hP Θ _ _ ε γ a₀ N)
  intro ξ
  have hh := curvatureOriginal_sosp_one_eighth (P ξ) hm hT (ε := ε) hL hγ R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  simpa only [pmfEventProbability_mean, curvatureOriginalJointLaw, finiteConditionalPMF_mean] using hh

/-- One deterministic hidden vector family defeats the randomized algorithm
over both its private seed and its oracle samples. The target is outside the
seed integral, as required by the lower-bound quantifiers. -/
theorem curvatureSeeded_exists_hard_target (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → CurvaturePolicy m T S) (hP : MeasurableQueryPolicyFamily P)
    (hm : 0<m) (hT : 0<T) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (CurvatureDimension m T)) (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536)
    (hfar : 512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤((2*m:ℕ):ℝ)) :
    ∃ Θ : Fin (T+1) → BalancedVector m, curvatureSeededSospProbability μ P Θ
      (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) R hR ε γ a₀ N<1/4 := by
  have hh := curvatureSeeded_sosp_one_eighth μ P hP hm hT (ε := ε) hL hγ R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  exact exists_below_pmfMean_bound (curvatureHiddenPrior m T) _
    (lt_of_le_of_lt hh (by norm_num))

end
end SecondOrder
