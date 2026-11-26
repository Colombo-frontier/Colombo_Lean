import SecondOrder.KernelEntryIndependence

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

theorem product_event_le_prior_bound (ρ : Measure H) [SFinite ρ]
    (ν : Measure S) [SFinite ν] {F : Set (H × S)} (hF : MeasurableSet F) {q : ℝ≥0∞}
    (htail : ∀ s, ρ {θ | (θ,s) ∈ F}≤q) : (ρ.prod ν) F≤q*ν Set.univ := by
  rw [Measure.prod_apply_symm hF]
  exact (lintegral_mono (fun s => htail s)).trans_eq (lintegral_const q)

/-- A fresh-block tail bound on an actual entry slice, retaining its true
entry mass. In particular the bound also holds for zero-mass slices. -/
theorem adaptiveKernelLaw_entry_tail (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, finiteHistoryMapInitial Prod.snd n h ∈ safe n →
      K n h = Q n (finiteHistoryMapInitial Prod.snd n h))
    (n : ℕ) {E : Set (FiniteHistory S A n)} (hE : MeasurableSet E)
    (hsub : E ⊆ kernelBeforeSet safe n)
    {F : Set (H × FiniteHistory S A n)} (hF : MeasurableSet F) {q : ℝ≥0∞}
    (htail : ∀ s, ρ {θ | (θ,s) ∈ F}≤q) :
    adaptiveKernelLaw (ρ.prod μ) K n
      {h | ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h) ∈ F ∧
        finiteHistoryMapInitial Prod.snd n h ∈ E} ≤ q*(adaptiveKernelLaw μ Q n) E := by
  have he := congrArg (fun η : Measure (H × FiniteHistory S A n) => η F)
    (adaptiveKernelLaw_entry_independent ρ μ K Q safe hs heq n hE hsub)
  change (((adaptiveKernelLaw (ρ.prod μ) K n).restrict (finiteHistoryMapInitial Prod.snd n ⁻¹' E)).map
    (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h))) F =
    (ρ.prod ((adaptiveKernelLaw μ Q n).restrict E)) F at he
  rw [Measure.map_apply (historyHiddenPair_measurable n) hF,
    Measure.restrict_apply (hF.preimage (historyHiddenPair_measurable n))] at he
  change adaptiveKernelLaw (ρ.prod μ) K n
    ((fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) ⁻¹' F ∩
      finiteHistoryMapInitial Prod.snd n ⁻¹' E) ≤ _
  rw [he]
  simpa only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using
    product_event_le_prior_bound ρ ((adaptiveKernelLaw μ Q n).restrict E) hF htail

end
end SecondOrder
