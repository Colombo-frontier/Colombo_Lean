import SecondOrder.HistoryRebase

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

theorem kernelContinuation_apply_succ (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n k : ℕ) (h : FiniteHistory S A n) :
    kernelContinuation K n (k+1) h=kernelContinuation K n k h ⊗ₘ K (n+k) := by
  rw [Measure.compProd_eq_comp_prod]
  rfl

/-- Reindexing a complete entry history changes neither subsequent replies
nor their actual joint law. -/
theorem rebasedKernelLaw_lintegral (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) (η : Measure (FiniteHistory S A n)) [IsProbabilityMeasure η] :
    ∀ k (F : FiniteHistory S A (n+k) → ℝ≥0∞), Measurable F →
      (∫⁻ h, F (historyRebase n k h) ∂adaptiveKernelLaw η (rebasedResponseKernel K n) k) =
      ∫⁻ h₀, ∫⁻ h, F h ∂kernelContinuation K n k h₀ ∂η := by
  intro k
  induction k with
  | zero =>
    intro F hF
    change (∫⁻ h, F h ∂η)=(∫⁻ h₀, ∫⁻ h, F h ∂Measure.dirac h₀ ∂η)
    apply lintegral_congr_ae
    filter_upwards [] with h₀
    exact (lintegral_dirac' h₀ hF).symm
  | succ k ih =>
    intro F hF
    let G : FiniteHistory S A (n+k) → ℝ≥0∞ := fun h => ∫⁻ a, F (h,a) ∂K (n+k) h
    have hG : Measurable G := Measurable.lintegral_kernel_prod_right (κ := K (n+k)) hF
    change (∫⁻ h, F (historyRebase n k h.1,h.2)
      ∂(adaptiveKernelLaw η (rebasedResponseKernel K n) k ⊗ₘ rebasedResponseKernel K n k)) = _
    rw [Measure.lintegral_compProd]
    · change (∫⁻ h, G (historyRebase n k h) ∂adaptiveKernelLaw η (rebasedResponseKernel K n) k) = _
      rw [ih G hG]
      apply lintegral_congr_ae
      filter_upwards [] with h₀
      rw [kernelContinuation_apply_succ]
      exact (Measure.lintegral_compProd (μ := kernelContinuation K n k h₀) (κ := K (n+k)) hF).symm
    · exact hF.comp (((historyRebase_measurable n k).comp measurable_fst).prodMk measurable_snd)

theorem rebasedKernelLaw_event (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) (η : Measure (FiniteHistory S A n)) [IsProbabilityMeasure η]
    (k : ℕ) {E : Set (FiniteHistory S A (n+k))} (hE : MeasurableSet E) :
    adaptiveKernelLaw η (rebasedResponseKernel K n) k (historyRebase n k ⁻¹' E) =
      ∫⁻ h₀, kernelContinuation K n k h₀ E ∂η := by
  rw [←lintegral_indicator_one (hE.preimage (historyRebase_measurable n k))]
  change (∫⁻ h, E.indicator (fun _ => (1:ℝ≥0∞)) (historyRebase n k h)
    ∂adaptiveKernelLaw η (rebasedResponseKernel K n) k) = _
  rw [rebasedKernelLaw_lintegral K n η k _ (measurable_const.indicator hE)]
  apply lintegral_congr_ae
  filter_upwards [] with h₀
  exact (lintegral_indicator_const hE (1:ℝ≥0∞)).trans (one_mul _)

theorem rebasedKernelLaw_map (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) (η : Measure (FiniteHistory S A n)) [IsProbabilityMeasure η] (k : ℕ) :
    (adaptiveKernelLaw η (rebasedResponseKernel K n) k).map (historyRebase n k)=kernelContinuation K n k ∘ₘ η := by
  ext E hE
  rw [Measure.map_apply (historyRebase_measurable n k) hE,
    Measure.bind_apply hE (kernelContinuation K n k).aemeasurable]
  exact rebasedKernelLaw_event K n η k hE

end
end SecondOrder
