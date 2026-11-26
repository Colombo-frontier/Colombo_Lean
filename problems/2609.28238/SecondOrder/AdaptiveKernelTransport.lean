import SecondOrder.KernelHiddenIndependence

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {S U A : Type u} [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace A]

def historyTransportKernel (K : ∀ n, Kernel (FiniteHistory U A n) A)
    (f : ∀ n, FiniteHistory S A n → FiniteHistory U A n) (hf : ∀ n, Measurable (f n))
    (n : ℕ) : Kernel (FiniteHistory S A n) A := (K n).comap (f n) (hf n)

instance historyTransportKernel_markov (K : ∀ n, Kernel (FiniteHistory U A n) A)
    [∀ n, IsMarkovKernel (K n)]
    (f : ∀ n, FiniteHistory S A n → FiniteHistory U A n) (hf : ∀ n, Measurable (f n)) (n : ℕ) :
    IsMarkovKernel (historyTransportKernel K f hf n) := by
  unfold historyTransportKernel
  infer_instance

/-- A measurable change of initial-state coordinates, retaining every
actual reply, transports the full adaptive distribution exactly. -/
theorem adaptiveKernelLaw_transport_lintegral (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory U A n) A) [∀ n, IsMarkovKernel (K n)]
    (f : ∀ n, FiniteHistory S A n → FiniteHistory U A n) (hf : ∀ n, Measurable (f n))
    (hstep : ∀ n h a, f (n+1) (h,a)=(f n h,a)) :
    ∀ n (F : FiniteHistory U A n → ℝ≥0∞), Measurable F →
      (∫⁻ h, F (f n h) ∂adaptiveKernelLaw μ (historyTransportKernel K f hf) n)=
      ∫⁻ h, F h ∂adaptiveKernelLaw (μ.map (f 0)) K n := by
  letI : IsProbabilityMeasure (μ.map (f 0)) := isProbabilityMeasure_map (hf 0).aemeasurable
  intro n
  induction n with
  | zero => intro F hF; exact (lintegral_map hF (hf 0)).symm
  | succ n ih =>
    intro F hF
    change (∫⁻ h, F (f (n+1) h) ∂(adaptiveKernelLaw μ (historyTransportKernel K f hf) n ⊗ₘ
      historyTransportKernel K f hf n))=∫⁻ h, F h ∂(adaptiveKernelLaw (μ.map (f 0)) K n ⊗ₘ K n)
    have hm : Measurable (fun h : FiniteHistory S A (n+1) => F (f (n+1) h)) := hF.comp (hf (n+1))
    rw [Measure.lintegral_compProd (μ := adaptiveKernelLaw μ (historyTransportKernel K f hf) n)
      (κ := historyTransportKernel K f hf n) hm,
      Measure.lintegral_compProd (μ := adaptiveKernelLaw (μ.map (f 0)) K n) (κ := K n) hF]
    simp only [hstep,historyTransportKernel,Kernel.comap_apply]
    exact ih (fun h => ∫⁻ a, F (h,a) ∂K n h) (Measurable.lintegral_kernel_prod_right hF)

theorem adaptiveKernelLaw_transport_map (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory U A n) A) [∀ n, IsMarkovKernel (K n)]
    (f : ∀ n, FiniteHistory S A n → FiniteHistory U A n) (hf : ∀ n, Measurable (f n))
    (hstep : ∀ n h a, f (n+1) (h,a)=(f n h,a)) (n : ℕ) :
    (adaptiveKernelLaw μ (historyTransportKernel K f hf) n).map (f n)=
      adaptiveKernelLaw (μ.map (f 0)) K n := by
  ext E hE
  rw [Measure.map_apply (hf n) hE,←lintegral_indicator_one (hE.preimage (hf n))]
  change (∫⁻ h, E.indicator (fun _ => (1:ℝ≥0∞)) (f n h)
    ∂adaptiveKernelLaw μ (historyTransportKernel K f hf) n)=_
  rw [adaptiveKernelLaw_transport_lintegral μ K f hf hstep n _ (measurable_const.indicator hE)]
  exact (lintegral_indicator_const hE (1:ℝ≥0∞)).trans (one_mul _)

end
end SecondOrder
