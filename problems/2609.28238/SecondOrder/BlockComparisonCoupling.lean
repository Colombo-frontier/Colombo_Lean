import SecondOrder.BlockComparisonKernel

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockNoFarSet (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ) :
    Set (FiniteHistory ((Fin T → H) × S) A n) :=
  {h | ∀ i, blockHistoryProgress active query n h+1 ≤ i.val →
    ¬ active i ((finiteHistoryInitial n h).1 i) (query n (finiteHistoryMapInitial Prod.snd n h))}

theorem blockNoFarSet_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) :
    MeasurableSet (blockNoFarSet active query n) := by
  have he : blockNoFarSet active query n = ⋂ i : Fin T,
      ({h | blockHistoryProgress active query n h+1 ≤ i.val} ∩
        {h | active i ((finiteHistoryInitial n h).1 i) (query n (finiteHistoryMapInitial Prod.snd n h))})ᶜ := by
    ext h
    simp only [blockNoFarSet,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_compl_iff,Set.mem_inter_iff,not_and]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact ((measurableSet_le ((blockHistoryProgress_measurable active ha query hq n).add_const 1)
    measurable_const).inter ((ha i).preimage
      (((measurable_pi_apply i).comp (measurable_fst.comp (finiteHistoryInitial_measurable n))).prodMk
        ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))))).compl

theorem blockActualKernel_eq_comparison (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) (hs : h ∈ blockNoFarSet active query n) :
    blockActualKernel active ha query hq O n h=blockComparisonKernel active ha query hq O n h := by
  change O (blockActivationIndex active (finiteHistoryInitial n h).1
    (query n (finiteHistoryMapInitial Prod.snd n h)) T) (blockHistoryInput query n h) =
    O (blockActivationIndex active (finiteHistoryInitial n h).1
      (query n (finiteHistoryMapInitial Prod.snd n h)) (blockHistoryProgress active query n h+1))
      (blockHistoryInput query n h)
  rw [blockActivationIndex_no_far active (finiteHistoryInitial n h).1
    (query n (finiteHistoryMapInitial Prod.snd n h)) (blockHistoryProgress active query n h+1) hs]

def blockHistoryFinish (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) : ℕ :=
  max (blockHistoryProgress active query n h) (blockHistoryIndex active query n h)

theorem blockHistoryFinish_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) :
    Measurable (blockHistoryFinish active query n) :=
  (blockHistoryProgress_measurable active ha query hq n).max
    (blockHistoryIndex_measurable active ha query hq n)

theorem blockHistoryFinish_eq_all_active (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) (hs : h ∈ blockNoFarSet active query n)
    (hactive : ∀ i, active i ((finiteHistoryInitial n h).1 i)
      (query n (finiteHistoryMapInitial Prod.snd n h))) : blockHistoryFinish active query n h=T := by
  have hi : blockHistoryIndex active query n h=T :=
    (blockActivationIndex_no_far active _ _ _ hs).trans (blockActivationIndex_all_active active _ _ hactive)
  unfold blockHistoryFinish
  rw [hi]
  exact max_eq_right (blockComparisonProgress_le active query _ n _)

theorem measure_event_transfer_of_restrict_eq {B : Type*} [MeasurableSpace B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {safe success complete : Set B} (hsafe : MeasurableSet safe) (hsuccess : MeasurableSet success)
    (heq : P.restrict safe=Q.restrict safe) (hsub : success ∩ safe ⊆ complete) :
    P.real success ≤ Q.real complete+Q.real safeᶜ := by
  have he := congrArg (fun η : Measure B => η.real success) heq
  simp only [measureReal_restrict_apply hsuccess] at he
  have hm := congrArg (fun η : Measure B => η Set.univ) heq
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hm
  have hc : P.real safeᶜ=Q.real safeᶜ := by
    simp only [measureReal_def,measure_compl hsafe (measure_ne_top _ _),measure_univ,hm]
  calc
    _ ≤ P.real ((success ∩ safe) ∪ safeᶜ) := measureReal_mono (by intro x hx; by_cases hh : x∈safe <;> simp [hx,hh])
    _ ≤ P.real (success ∩ safe)+P.real safeᶜ := measureReal_union_le _ _
    _ = Q.real (success ∩ safe)+Q.real safeᶜ := by rw [he,hc]
    _ ≤ Q.real complete+Q.real safeᶜ := add_le_add_right (measureReal_mono hsub) _

/-- Genuine success is bounded by comparison completion plus comparison
far jumps. This includes the final output without sampling a final reply. -/
theorem blockActual_success_le_comparison (μ : Measure ((Fin T → H) × S)) [IsProbabilityMeasure μ]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (N : ℕ)
    (success : Set (FiniteHistory ((Fin T → H) × S) A N)) (hm : MeasurableSet success)
    (hactive : ∀ h ∈ success, ∀ i, active i ((finiteHistoryInitial N h).1 i)
      (query N (finiteHistoryMapInitial Prod.snd N h))) :
    (adaptiveKernelLaw μ (blockActualKernel active ha query hq O) N).real success ≤
      (adaptiveKernelLaw μ (blockComparisonKernel active ha query hq O) N).real
        {h | blockHistoryFinish active query N h=T}+
      (adaptiveKernelLaw μ (blockComparisonKernel active ha query hq O) N).real
        (kernelSurvivalSet (blockNoFarSet active query) N)ᶜ := by
  apply measure_event_transfer_of_restrict_eq _ _
    (kernelSurvivalSet_measurable _ (blockNoFarSet_measurable active ha query hq) N) hm
    (adaptiveKernelLaw_survival_eq μ _ _ (blockNoFarSet active query)
      (blockNoFarSet_measurable active ha query hq) (blockActualKernel_eq_comparison active ha query hq O) N)
  intro h hh
  exact blockHistoryFinish_eq_all_active active query N h
    (kernelSurvivalSet_subset _ N hh.2) (hactive h hh.1)

end
end SecondOrder
