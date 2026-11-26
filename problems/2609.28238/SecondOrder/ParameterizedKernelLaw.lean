import SecondOrder.KernelHiddenIndependence
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- The complete public-history law, as a measurable kernel of the fixed
hidden parameter. The seed law stays independent of that parameter. -/
def parameterHistoryKernel (μ : Measure S) (K : ∀ n, Kernel (H × FiniteHistory S A n) A) :
    (n : ℕ) → Kernel H (FiniteHistory S A n)
  | 0 => Kernel.const H μ
  | n+1 => parameterHistoryKernel μ K n ⊗ₖ K n

instance parameterHistoryKernel_markov (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] :
    ∀ n, IsMarkovKernel (parameterHistoryKernel μ K n)
  | 0 => inferInstanceAs (IsMarkovKernel (Kernel.const H μ))
  | n+1 => by
    letI := parameterHistoryKernel_markov μ K n
    exact inferInstanceAs (IsMarkovKernel (parameterHistoryKernel μ K n ⊗ₖ K n))

theorem parameterHistoryKernel_apply (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] (θ : H) :
    ∀ n, parameterHistoryKernel μ K n θ = adaptiveKernelLaw μ (fun n => (K n).sectR θ) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (parameterHistoryKernel μ K n ⊗ₖ K n) θ = _
    rw [Kernel.compProd_apply_eq_compProd_sectR,ih]
    rfl

def parameterizedResponseKernel (K : ∀ n, Kernel (H × FiniteHistory S A n) A) (n : ℕ) :
    Kernel (FiniteHistory (H × S) A n) A :=
  (K n).comap (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))
    (historyHiddenPair_measurable n)

instance parameterizedResponseKernel_markov (K : ∀ n, Kernel (H × FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) : IsMarkovKernel (parameterizedResponseKernel K n) := by
  unfold parameterizedResponseKernel
  infer_instance

/-- Exact mixture over the hidden prior for the actual adaptive response
experiment. Every section is a complete interaction with that parameter. -/
theorem adaptiveKernelLaw_parameter_lintegral (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] :
    ∀ n (F : H × FiniteHistory S A n → ℝ≥0∞), Measurable F →
      (∫⁻ h, F ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n) =
      ∫⁻ θ, ∫⁻ h, F (θ,h) ∂adaptiveKernelLaw μ (fun n => (K n).sectR θ) n ∂ρ := by
  intro n
  induction n with
  | zero => intro F hF; exact lintegral_prod _ hF.aemeasurable
  | succ n ih =>
    intro F hF
    let G : H × FiniteHistory S A n → ℝ≥0∞ := fun z => ∫⁻ a, F (z.1,(z.2,a)) ∂K n z
    have hG : Measurable G := Measurable.lintegral_kernel_prod_right
      (κ := K n) (hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
    change (∫⁻ h, F ((finiteHistoryInitial n h.1).1,(finiteHistoryMapInitial Prod.snd n h.1,h.2))
      ∂(adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n ⊗ₘ parameterizedResponseKernel K n)) = _
    rw [Measure.lintegral_compProd]
    · change (∫⁻ h, G ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
        ∂adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n) = _
      rw [ih G hG]
      apply lintegral_congr_ae
      filter_upwards [] with θ
      exact (Measure.lintegral_compProd (μ := adaptiveKernelLaw μ (fun n => (K n).sectR θ) n)
        (κ := (K n).sectR θ) (hF.comp measurable_prodMk_left)).symm
    · exact hF.comp ((measurable_fst.comp (finiteHistoryInitial_measurable n)).comp measurable_fst |>.prodMk
        (((finiteHistoryMapInitial_measurable measurable_snd n).comp measurable_fst).prodMk measurable_snd))

theorem adaptiveKernelLaw_parameter_event (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (n : ℕ) {E : Set (H × FiniteHistory S A n)} (hE : MeasurableSet E) :
    adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n
      {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ E} =
      ∫⁻ θ, adaptiveKernelLaw μ (fun n => (K n).sectR θ) n {h | (θ,h) ∈ E} ∂ρ := by
  change adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n
    ((fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) ⁻¹' E) = _
  rw [←lintegral_indicator_one (hE.preimage (historyHiddenPair_measurable n))]
  change (∫⁻ h, E.indicator (fun _ => (1:ℝ≥0∞))
    ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)
      ∂adaptiveKernelLaw (ρ.prod μ) (parameterizedResponseKernel K) n) = _
  rw [adaptiveKernelLaw_parameter_lintegral ρ μ K n _ (measurable_const.indicator hE)]
  apply lintegral_congr_ae
  filter_upwards [] with θ
  exact (lintegral_indicator_const (hE.preimage measurable_prodMk_left) (1:ℝ≥0∞)).trans (one_mul _)

theorem parameterHistory_event_measurable (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H × FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (n : ℕ) {E : Set (H × FiniteHistory S A n)} (hE : MeasurableSet E) :
    Measurable (fun θ => adaptiveKernelLaw μ (fun n => (K n).sectR θ) n {h | (θ,h) ∈ E}) := by
  simp_rw [←parameterHistoryKernel_apply μ K]
  exact Kernel.measurable_kernel_prodMk_left hE

end
end SecondOrder
