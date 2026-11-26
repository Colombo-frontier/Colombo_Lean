import SecondOrder.HistoryHiddenEquiv
import SecondOrder.KernelContinuation

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- The exact original continuation law on an independent entry slice.
The public entry measure may have any finite mass, including zero. -/
theorem kernelHiddenContinuation_event (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (n k : ℕ)
    (η : Measure (FiniteHistory (H × S) A n)) (ρ : Measure H) [SFinite ρ]
    (ν : Measure (FiniteHistory S A n)) [SFinite ν]
    (hη : η.map (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))=ρ.prod ν)
    {E : Set (FiniteHistory (H × S) A (n+k))} (hE : MeasurableSet E) :
    (kernelContinuation K n k ∘ₘ η) E =
      ∫⁻ θ, ∫⁻ h, kernelContinuation K n k (historyJoinHidden n (θ,h)) E ∂ν ∂ρ := by
  rw [Measure.bind_apply hE (kernelContinuation K n k).aemeasurable,
    entryMeasure_eq_join_map n η ρ ν hη,
    lintegral_map ((kernelContinuation K n k).measurable_coe hE) (historyJoinHidden_measurable n)]
  exact lintegral_prod _ (((kernelContinuation K n k).measurable_coe hE).comp (historyJoinHidden_measurable n)).aemeasurable

theorem kernelHiddenContinuation_bound (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (n k : ℕ)
    (η : Measure (FiniteHistory (H × S) A n)) (ρ : Measure H) [SFinite ρ]
    (ν : Measure (FiniteHistory S A n)) [SFinite ν]
    (hη : η.map (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))=ρ.prod ν)
    {E : Set (FiniteHistory (H × S) A (n+k))} (hE : MeasurableSet E) {q : ℝ≥0∞}
    (hfuture : ∀ᵐ h ∂ν, (∫⁻ θ, kernelContinuation K n k (historyJoinHidden n (θ,h)) E ∂ρ)≤q) :
    (kernelContinuation K n k ∘ₘ η) E≤q*ν Set.univ := by
  rw [kernelHiddenContinuation_event K n k η ρ ν hη hE]
  have hm : Measurable (fun z : H × FiniteHistory S A n =>
      kernelContinuation K n k (historyJoinHidden n z) E) :=
    ((kernelContinuation K n k).measurable_coe hE).comp (historyJoinHidden_measurable n)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  exact (lintegral_mono_ae hfuture).trans_eq (lintegral_const q)

end
end SecondOrder
