import SecondOrder.HistoryResumeHidden
import SecondOrder.AdaptiveKernelTransport
import SecondOrder.RebasedKernelLaw

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

theorem resumedHiddenKernel_transport (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A) (n : ℕ) :
    historyTransportKernel (rebasedResponseKernel K n)
      (finiteHistoryMapInitial (historyJoinHidden n))
      (finiteHistoryMapInitial_measurable (historyJoinHidden_measurable n))=resumedHiddenKernel K n := by
  funext k
  apply Kernel.ext
  intro h
  simp only [historyTransportKernel,rebasedResponseKernel,resumedHiddenKernel,Kernel.comap_apply,
    historyResumeHidden_eq_rebase]

/-- Restarting with hidden/public entry coordinates has exactly the
original continuation law after the complete history is reconstructed. -/
theorem resumedHiddenLaw_map (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ)
    (μ : Measure (H × FiniteHistory S A n)) [IsProbabilityMeasure μ] (k : ℕ) :
    (adaptiveKernelLaw μ (resumedHiddenKernel K n) k).map (historyResumeHidden n k)=
      kernelContinuation K n k ∘ₘ (μ.map (historyJoinHidden n)) := by
  letI : IsProbabilityMeasure (μ.map (historyJoinHidden n)) :=
    isProbabilityMeasure_map (historyJoinHidden_measurable n).aemeasurable
  have ht := adaptiveKernelLaw_transport_map μ (rebasedResponseKernel K n)
    (finiteHistoryMapInitial (historyJoinHidden n))
    (finiteHistoryMapInitial_measurable (historyJoinHidden_measurable n)) (fun _ _ _ => rfl) k
  rw [resumedHiddenKernel_transport] at ht
  have he : historyResumeHidden (H := H) (S := S) (A := A) n k=
      historyRebase n k ∘ finiteHistoryMapInitial (historyJoinHidden n) k := by
    funext h
    exact historyResumeHidden_eq_rebase n k h
  rw [he,←Measure.map_map (historyRebase_measurable n k)
    (finiteHistoryMapInitial_measurable (historyJoinHidden_measurable n) k),ht]
  exact rebasedKernelLaw_map K n (μ.map (historyJoinHidden n)) k

theorem resumedHiddenLaw_event (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ)
    (μ : Measure (H × FiniteHistory S A n)) [IsProbabilityMeasure μ] (k : ℕ)
    {E : Set (FiniteHistory (H × S) A (n+k))} (hE : MeasurableSet E) :
    adaptiveKernelLaw μ (resumedHiddenKernel K n) k (historyResumeHidden n k ⁻¹' E)=
      ∫⁻ h, kernelContinuation K n k (historyJoinHidden n h) E ∂μ := by
  rw [←Measure.map_apply (historyResumeHidden_measurable n k) hE,resumedHiddenLaw_map,
    Measure.bind_apply hE (kernelContinuation K n k).aemeasurable,
    lintegral_map ((kernelContinuation K n k).measurable_coe hE) (historyJoinHidden_measurable n)]

/-- Pointwise public entry histories can be averaged against the hidden
prior before integrating over an unnormalised random-entry law. -/
theorem resumedHiddenLaw_prior_event (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    [∀ n, IsMarkovKernel (K n)] (ρ : Measure H) [IsProbabilityMeasure ρ]
    (n : ℕ) (h₀ : FiniteHistory S A n) (k : ℕ)
    {E : Set (FiniteHistory (H × S) A (n+k))} (hE : MeasurableSet E) :
    adaptiveKernelLaw (ρ.prod (Measure.dirac h₀)) (resumedHiddenKernel K n) k
      (historyResumeHidden n k ⁻¹' E)=
      ∫⁻ θ, kernelContinuation K n k (historyJoinHidden n (θ,h₀)) E ∂ρ := by
  rw [resumedHiddenLaw_event K n (ρ.prod (Measure.dirac h₀)) k hE]
  have hm : Measurable (fun h : H × FiniteHistory S A n =>
      kernelContinuation K n k (historyJoinHidden n h) E) :=
    ((kernelContinuation K n k).measurable_coe hE).comp (historyJoinHidden_measurable n)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [] with θ
  exact lintegral_dirac' h₀ (hm.comp measurable_prodMk_left)

end
end SecondOrder
