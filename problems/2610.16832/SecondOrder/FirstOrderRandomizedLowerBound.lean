import SecondOrder.FirstOrderRandomizedSuccess

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {d T : ℕ}

def HasFirstOrderCertificate {n : ℕ} (F : Point n → ℝ) (ε : ℝ) (x : Point n) : Prop :=
  ‖gradient F x‖≤ε

theorem hasFirstOrderCertificate_measurableSet {n : ℕ} {F : Point n → ℝ}
    (hF : ContDiff ℝ 2 F) (ε : ℝ) : MeasurableSet {x | HasFirstOrderCertificate F ε x} :=
  measurableSet_le (contDiff_gradient_one hF).continuous.norm.measurable measurable_const

/-- The hidden instance is selected after integrating all private seeds. -/
theorem firstOrderSeeded_exists_hard_target (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (hP : MeasurableQueryPolicyFamily P)
    (hd : 0<d) (hT : 0<T) (A β R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ))
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop)
    (hsuccess : ∀ Θ, MeasurableSet {x | success Θ x})
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x)=T+1) :
    ∃ Θ : Fin (T+1) → Fin d → Bool,
      firstOrderSeededSuccessProbability μ P Θ A β R hR success a₀ N<1/4 := by
  have hh := firstOrderSeeded_success_one_eighth μ P hP hd hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar success hsuccess hcomplete
  exact exists_below_pmfMean_bound (firstOrderHiddenPrior d T) _ (lt_of_le_of_lt hh (by norm_num))

def firstOrderSeededGradientProbability (μ : Measure Ξ) (P : Ξ → FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β R : ℝ) (hR : 2≤R) (ε : ℝ)
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ) : ℝ :=
  firstOrderSeededSuccessProbability μ P Θ A β R hR
    (fun Θ x => HasFirstOrderCertificate (scaledFirstOrderPopulation Θ A β) ε x) a₀ N

theorem firstOrderSeeded_gradient_one_eighth (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (hP : MeasurableQueryPolicyFamily P)
    (hd : 0<d) (hT : 0<T) {A β ε : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ)) :
    pmfMean (firstOrderHiddenPrior d T)
      (fun Θ => firstOrderSeededGradientProbability μ P Θ A β R hR ε a₀ N)≤1/8 := by
  apply firstOrderSeeded_success_one_eighth μ P hP hd hT A β R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  · intro Θ
    exact hasFirstOrderCertificate_measurableSet
      ((scaledFirstOrderPopulation_contDiff Θ A β).of_le (show (2:WithTop ℕ∞)≤3 by decide)) ε
  · intro Θ x hx
    exact scaledFirstOrderPopulation_gradient_progress Θ hd hA hβ hε hx

theorem firstOrderSeeded_exists_gradient_hard_target (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (hP : MeasurableQueryPolicyFamily P)
    (hd : 0<d) (hT : 0<T) {A β ε : ℝ} (hA : 0≤A) (hβ : 0≤β)
    (hε : ε<A*β*firstOrderGradientConstant) (R : ℝ) (hR : 2≤R) (cap : ℕ) (hcap0 : 0<cap)
    (dummy : RichReply (FirstOrderDimension d T)) (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hbudget : 2*N≤T*cap)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤(d:ℝ)) :
    ∃ Θ : Fin (T+1) → Fin d → Bool,
      firstOrderSeededGradientProbability μ P Θ A β R hR ε a₀ N<1/4 := by
  have hh := firstOrderSeeded_gradient_one_eighth μ P hP hd hT hA hβ hε R hR cap hcap0 dummy a₀ N
    hbudget hhorizon hlarge hcap hfar
  exact exists_below_pmfMean_bound (firstOrderHiddenPrior d T) _ (lt_of_le_of_lt hh (by norm_num))

def firstOrderSeededSospProbability (μ : Measure Ξ) (P : Ξ → FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ)
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ) : ℝ :=
  firstOrderSeededSuccessProbability μ P Θ A β R hR
    (fun Θ x => IsSOSP (scaledFirstOrderPopulation Θ A β) ε γ x) a₀ N

theorem firstOrderSeededSospProbability_le_gradient (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderPolicy d T S) (Θ : Fin (T+1) → Fin d → Bool)
    (A β R : ℝ) (hR : 2≤R) (ε γ : ℝ) (a₀ : FirstOrderCoefficients d T R) (N : ℕ) :
    firstOrderSeededSospProbability μ P Θ A β R hR ε γ a₀ N≤
      firstOrderSeededGradientProbability μ P Θ A β R hR ε a₀ N := by
  unfold firstOrderSeededSospProbability firstOrderSeededGradientProbability firstOrderSeededSuccessProbability
  exact measureReal_mono (fun w hw => hw.1)

end
end SecondOrder
