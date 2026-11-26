import SecondOrder.BlockStageKernels
import SecondOrder.BlockStageCharges

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem blockActivationIndex_drop_inactive (active : Fin T → H → X → Prop)
    (Θ : Fin T → H) (x : X) (j : Fin T) (ha : ¬ active j (Θ j) x) :
    blockActivationIndex active Θ x (j.val+1)=blockActivationIndex active Θ x j.val := by
  unfold blockActivationIndex
  congr 1
  funext i
  by_cases he : i=j
  · subst i
    simp only [ha,and_false,if_false]
  · have hv : i.val≠j.val := fun hh => he (Fin.ext hh)
    have hc : (i.val<j.val+1)=(i.val<j.val) := propext (by omega)
    simp only [hc]

/-- Between entry and completion, suppressing inspection of an inactive
target leaves the chosen response index unchanged. -/
theorem blockComparisonIndex_eq_stage (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (θ : H)
    (n : ℕ) (h : FiniteHistory S A n)
    (hl : j.val≤blockComparisonProgress active query (Function.update Θ j θ) n h+1)
    (hu : blockComparisonProgress active query (Function.update Θ j θ) n h≤j.val)
    (hn : ¬ active j θ (query n h)) :
    blockComparisonIndex active query (Function.update Θ j θ) n h=blockStageIndex active query Θ j n h := by
  have hp : blockActivationIndex active (Function.update Θ j θ) (query n h) j.val =
      blockActivationIndex active Θ (query n h) j.val :=
    blockActivationIndex_prefix active _ _ _ _ (fun i hi =>
      Function.update_of_ne (by intro he; subst i; omega) _ _)
  unfold blockComparisonIndex blockStageIndex
  by_cases he : blockComparisonProgress active query (Function.update Θ j θ) n h+1=j.val
  · rw [he,hp]
  · have he' : blockComparisonProgress active query (Function.update Θ j θ) n h=j.val := by omega
    rw [he',blockActivationIndex_drop_inactive active _ _ j (by simpa only [Function.update_self] using hn),hp]

theorem blockTargetKernel_eq_stage (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T)
    (n : ℕ) (h : FiniteHistory (H × S) A n)
    (hl : j.val≤blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial n h).1)
      n (finiteHistoryMapInitial Prod.snd n h)+1)
    (hu : blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial n h).1)
      n (finiteHistoryMapInitial Prod.snd n h)≤j.val)
    (hn : ¬ active j (finiteHistoryInitial n h).1 (query n (finiteHistoryMapInitial Prod.snd n h))) :
    blockTargetKernel active ha query hq O Θ j n h=blockStageTrueKernel active ha query hq O Θ j n h := by
  rw [blockTargetKernel_apply,blockComparisonIndex_eq_stage active query Θ j _ n _ hl hu hn]
  rfl

/-- Before the charge cap and the target activation, the actual comparison
reply agrees with the capped stage reply. -/
theorem blockTargetKernel_eq_capped_stage (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T)
    (cap : ℕ) (dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    (n : ℕ) (h : FiniteHistory (H × S) A n)
    (hl : j.val≤blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial n h).1)
      n (finiteHistoryMapInitial Prod.snd n h)+1)
    (hu : blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial n h).1)
      n (finiteHistoryMapInitial Prod.snd n h)≤j.val)
    (hn : ¬ active j (finiteHistoryInitial n h).1 (query n (finiteHistoryMapInitial Prod.snd n h)))
    (hc : kernelChargeCount (stageSelected (blockStageSelected active query Θ j)) cap n h<cap) :
    blockTargetKernel active ha query hq O Θ j n h=
      cappedResponseKernel (stageSelected (blockStageSelected active query Θ j))
        (stageSelected_measurable _ (blockStageSelected_measurable active ha query hq Θ j)) cap
        (blockStageTrueKernel active ha query hq O Θ j) (hiddenIndependentKernel dummy) n h := by
  simp only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_pos hc]
  exact blockTargetKernel_eq_stage active ha query hq O Θ j n h hl hu hn

end
end SecondOrder
