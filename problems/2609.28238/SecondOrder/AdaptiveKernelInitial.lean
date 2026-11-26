import SecondOrder.KernelHiddenIndependence

open MeasureTheory ProbabilityTheory

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

theorem adaptiveKernelLaw_initial_event (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    {E : Set S} (hE : MeasurableSet E) :
    ∀ n, adaptiveKernelLaw μ K n (finiteHistoryInitial n ⁻¹' E)=μ E := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (adaptiveKernelLaw μ K n ⊗ₘ K n) (Prod.fst ⁻¹' (finiteHistoryInitial n ⁻¹' E))=μ E
    rw [←Measure.fst_apply (hE.preimage (finiteHistoryInitial_measurable n)),Measure.fst_compProd]
    exact ih

theorem adaptiveKernelLaw_initial_map (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (adaptiveKernelLaw μ K n).map (finiteHistoryInitial n)=μ := by
  ext E hE
  rw [Measure.map_apply (finiteHistoryInitial_measurable n) hE]
  exact adaptiveKernelLaw_initial_event μ K hE n

/-- Every almost-sure property of the initial seed/entry coordinates
remains true along the full adaptive history. -/
theorem adaptiveKernelLaw_initial_ae (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    {P : S → Prop} (hP : ∀ᵐ s ∂μ, P s) (n : ℕ) :
    ∀ᵐ h ∂adaptiveKernelLaw μ K n, P (finiteHistoryInitial n h) := by
  apply ae_of_ae_map (finiteHistoryInitial_measurable n).aemeasurable
  rwa [adaptiveKernelLaw_initial_map μ K n]

end
end SecondOrder
