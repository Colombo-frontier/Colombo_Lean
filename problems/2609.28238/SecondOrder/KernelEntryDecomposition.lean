import SecondOrder.KernelToTime
import SecondOrder.KernelFirstEntry

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

theorem kernel_comp_finset_sum {B C ι : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (K : Kernel B C) (s : Finset ι) (μ : ι → Measure B) :
    K ∘ₘ (∑ i ∈ s, μ i)=∑ i ∈ s, K ∘ₘ μ i := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Measure.bind_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Measure.comp_add,ih]

theorem kernelEntry_restrict_partition (μ : Measure (FiniteHistory S A n))
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) :
    μ.restrict (kernelBeforeSet safe n)=
      μ.restrict (kernelSurvivalSet safe n)+μ.restrict (kernelFirstExitSet safe n) := by
  have he : kernelSurvivalSet safe n ∪ kernelFirstExitSet safe n=kernelBeforeSet safe n := by
    rw [kernelSurvivalSet_eq_inter_before]
    ext h
    simp only [kernelFirstExitSet,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
    tauto
  have hd : Disjoint (kernelSurvivalSet safe n) (kernelFirstExitSet safe n) := by
    apply Set.disjoint_left.mpr
    intro h hh hh'
    exact hh'.2 (kernelSurvivalSet_subset safe n hh)
  rw [←he,Measure.restrict_union hd (kernelFirstExitSet_measurable safe hs n)]

theorem adaptiveKernelLaw_before_measure (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (n : ℕ) :
    (adaptiveKernelLaw μ K (n+1)).restrict (kernelBeforeSet safe (n+1))=
      (Kernel.id ×ₖ K n) ∘ₘ ((adaptiveKernelLaw μ K n).restrict (kernelSurvivalSet safe n)) := by
  change (adaptiveKernelLaw μ K n ⊗ₘ K n).restrict (Prod.fst ⁻¹' kernelSurvivalSet safe n)=_
  rw [compProd_restrict_history _ _ (kernelSurvivalSet_measurable safe hs n),Measure.compProd_eq_comp_prod]

/-- The entire actual terminal law is the sum of every first-entry
continuation and the still-unentered terminal restriction. This is an
identity of measures, so it applies to arbitrary measurable terminal events. -/
theorem adaptiveKernelLaw_entry_decomposition (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) :
    ∀ N, adaptiveKernelLaw μ K N =
      (adaptiveKernelLaw μ K N).restrict (kernelSurvivalSet safe N)+
      ∑ n ∈ Finset.range (N+1), kernelToTime K n N ∘ₘ
        ((adaptiveKernelLaw μ K n).restrict (kernelFirstExitSet safe n)) := by
  intro N
  induction N with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one,kernelToTime_self,Measure.id_comp]
    simpa only [kernelBeforeSet,Measure.restrict_univ] using kernelEntry_restrict_partition μ safe hs (n := 0)
  | succ N ih =>
    have he : ∀ n ∈ Finset.range (N+1), (Kernel.id ×ₖ K N) ∘ₘ
        (kernelToTime K n N ∘ₘ (adaptiveKernelLaw μ K n).restrict (kernelFirstExitSet safe n))=
        kernelToTime K n (N+1) ∘ₘ (adaptiveKernelLaw μ K n).restrict (kernelFirstExitSet safe n) := by
      intro n hn
      rw [Measure.comp_assoc,←kernelToTime_succ K (by have := Finset.mem_range.mp hn; omega)]
      rfl
    change (adaptiveKernelLaw μ K N ⊗ₘ K N)=_
    rw [Measure.compProd_eq_comp_prod,ih,Measure.comp_add,kernel_comp_finset_sum,
      ←adaptiveKernelLaw_before_measure μ K safe hs N,kernelEntry_restrict_partition _ safe hs,
      Finset.sum_congr rfl he]
    conv_rhs => rw [Finset.sum_range_succ,kernelToTime_self,Measure.id_comp]
    rw [add_assoc]
    congr 1
    exact add_comm _ _

theorem adaptiveKernelLaw_entry_event (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (N : ℕ)
    {E : Set (FiniteHistory S A N)} (hE : MeasurableSet E)
    (hd : Disjoint E (kernelSurvivalSet safe N)) :
    adaptiveKernelLaw μ K N E=∑ n ∈ Finset.range (N+1),
      (kernelToTime K n N ∘ₘ ((adaptiveKernelLaw μ K n).restrict (kernelFirstExitSet safe n))) E := by
  have he := congrArg (fun η : Measure (FiniteHistory S A N) => η E)
    (adaptiveKernelLaw_entry_decomposition μ K safe hs N)
  simpa only [Measure.add_apply,Measure.finset_sum_apply,Measure.restrict_apply hE,
    Set.disjoint_iff_inter_eq_empty.mp hd,measure_empty,zero_add] using he

end
end SecondOrder
