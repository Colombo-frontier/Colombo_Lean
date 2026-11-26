import SecondOrder.KernelEntryIndependence

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

/-- First failed safety test, at the current pre-response query. -/
def kernelFirstExitSet (safe : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) :
    Set (FiniteHistory S A n) := kernelBeforeSet safe n ∩ (safe n)ᶜ

theorem kernelFirstExitSet_measurable (safe : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) (n : ℕ) : MeasurableSet (kernelFirstExitSet safe n) :=
  (kernelBeforeSet_measurable safe hs n).inter (hs n).compl

theorem adaptiveKernelLaw_before_probability (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (n : ℕ) :
    (adaptiveKernelLaw μ K (n+1)).real (kernelBeforeSet safe (n+1)) =
      (adaptiveKernelLaw μ K n).real (kernelSurvivalSet safe n) := by
  unfold Measure.real
  change ((adaptiveKernelLaw μ K n ⊗ₘ K n) (Prod.fst ⁻¹' kernelSurvivalSet safe n)).toReal = _
  rw [←Measure.fst_apply (kernelSurvivalSet_measurable safe hs n),Measure.fst_compProd]

theorem adaptiveKernelLaw_firstExit_partition (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (n : ℕ) :
    (adaptiveKernelLaw μ K n).real (kernelFirstExitSet safe n)+
      (adaptiveKernelLaw μ K n).real (kernelSurvivalSet safe n) =
      (adaptiveKernelLaw μ K n).real (kernelBeforeSet safe n) := by
  have he : kernelFirstExitSet safe n ∪ kernelSurvivalSet safe n = kernelBeforeSet safe n := by
    rw [kernelSurvivalSet_eq_inter_before]
    ext h
    simp only [kernelFirstExitSet,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  have hd : Disjoint (kernelFirstExitSet safe n) (kernelSurvivalSet safe n) := by
    rw [kernelSurvivalSet_eq_inter_before]
    exact Set.disjoint_left.mpr (fun h hh hh' => hh.2 hh'.1)
  rw [←he,measureReal_union hd (kernelSurvivalSet_measurable safe hs n)]

/-- The entry masses telescope under the actual adaptive law. In
particular summing bounds over all possible entry times costs no horizon
factor. The final, possibly unqueried output is the test at time `N`. -/
theorem adaptiveKernelLaw_firstExit_total (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) :
    ∀ N, (∑ n ∈ Finset.range (N+1), (adaptiveKernelLaw μ K n).real (kernelFirstExitSet safe n))+
      (adaptiveKernelLaw μ K N).real (kernelSurvivalSet safe N) = 1 := by
  intro N
  induction N with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one]
    rw [adaptiveKernelLaw_firstExit_partition μ K safe hs 0]
    change (μ Set.univ).toReal = 1
    rw [measure_univ,ENNReal.toReal_one]
  | succ N ih =>
    rw [Finset.sum_range_succ,add_assoc,adaptiveKernelLaw_firstExit_partition μ K safe hs (N+1),
      adaptiveKernelLaw_before_probability μ K safe hs N]
    exact ih

theorem adaptiveKernelLaw_firstExit_sum_le_one (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), (adaptiveKernelLaw μ K n).real (kernelFirstExitSet safe n)) ≤ 1 := by
  have he := adaptiveKernelLaw_firstExit_total μ K safe hs N
  have hn := measureReal_nonneg (μ := adaptiveKernelLaw μ K N) (s := kernelSurvivalSet safe N)
  linarith

theorem adaptiveKernelLaw_firstEntry_independent (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, finiteHistoryMapInitial Prod.snd n h ∈ safe n →
      K n h = Q n (finiteHistoryMapInitial Prod.snd n h)) (n : ℕ) :
    ((adaptiveKernelLaw (ρ.prod μ) K n).restrict
      (finiteHistoryMapInitial Prod.snd n ⁻¹' kernelFirstExitSet safe n)).map
      (fun h => ((finiteHistoryInitial n h).1,finiteHistoryMapInitial Prod.snd n h)) =
      ρ.prod ((adaptiveKernelLaw μ Q n).restrict (kernelFirstExitSet safe n)) :=
  adaptiveKernelLaw_entry_independent ρ μ K Q safe hs heq n
    (kernelFirstExitSet_measurable safe hs n) Set.inter_subset_left

end
end SecondOrder
