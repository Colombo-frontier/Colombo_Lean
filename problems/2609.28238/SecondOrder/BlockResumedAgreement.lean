import SecondOrder.BlockStageAgreement
import SecondOrder.HistoryResumeHidden
import SecondOrder.KernelStoppedHit
import SecondOrder.KernelStageFirstActivation

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockResumedProgress (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n k : ℕ)
    (h : FiniteHistory (H × FiniteHistory S A n) A k) : ℕ :=
  blockComparisonProgress active query (Function.update Θ j (finiteHistoryInitial k h).1)
    (n+k) (historyRebase n k (finiteHistoryMapInitial Prod.snd k h))

theorem blockResumedProgress_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n k : ℕ) : Measurable (blockResumedProgress active query Θ j n k) :=
  (blockComparisonProgress_measurable active ha query hq (n+k)).comp
    (((measurable_update Θ).comp (measurable_fst.comp (finiteHistoryInitial_measurable k))).prodMk
      ((historyRebase_measurable n k).comp (finiteHistoryMapInitial_measurable measurable_snd k)))

def blockResumedActive (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (j : Fin T) (n k : ℕ) :
    Set (FiniteHistory (H × FiniteHistory S A n) A k) :=
  kernelHiddenEvent (fun k θ h => active j θ (rebasedQuery query n k h)) k

theorem blockResumedActive_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (j : Fin T) (n k : ℕ) : MeasurableSet (blockResumedActive active query j n k) :=
  kernelHiddenEvent_measurable (fun k θ h => active j θ (rebasedQuery query n k h)) (fun k => (ha j).preimage
    (measurable_fst.prodMk ((rebasedQuery_measurable query hq n k).comp measurable_snd))) k

def blockResumedSafe (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n cap k : ℕ) :
    Set (FiniteHistory (H × FiniteHistory S A n) A k) :=
  {h | j.val≤blockResumedProgress active query Θ j n k h+1 ∧
    blockResumedProgress active query Θ j n k h≤j.val ∧
    h ∉ blockResumedActive active query j n k ∧
    kernelChargeCount (stageSelected (blockStageSelected active (rebasedQuery query n) Θ j)) cap k h<cap}

theorem blockResumedSafe_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n cap k : ℕ) : MeasurableSet (blockResumedSafe active query Θ j n cap k) :=
  (measurableSet_le measurable_const ((blockResumedProgress_measurable active ha query hq Θ j n k).add_const 1)).inter
    ((measurableSet_le (blockResumedProgress_measurable active ha query hq Θ j n k) measurable_const).inter
      ((blockResumedActive_measurable active ha query hq j n k).compl.inter
        (measurableSet_lt (kernelChargeCount_measurable _
          (stageSelected_measurable _ (blockStageSelected_measurable active ha (rebasedQuery query n)
            (rebasedQuery_measurable query hq n) Θ j)) cap k) measurable_const)))

/-- The actual original target kernel, after retaining and rebasing its
entry history, agrees with the capped block stage until activation or cap. -/
theorem blockResumedKernel_eq_stage (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (n cap : ℕ)
    (dummy : ∀ k, Kernel (FiniteHistory (FiniteHistory S A n) A k) A)
    (k : ℕ) (h : FiniteHistory (H × FiniteHistory S A n) A k)
    (hs : h ∈ blockResumedSafe active query Θ j n cap k) :
    resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n k h=
      cappedResponseKernel (stageSelected (blockStageSelected active (rebasedQuery query n) Θ j))
        (stageSelected_measurable _ (blockStageSelected_measurable active ha (rebasedQuery query n)
          (rebasedQuery_measurable query hq n) Θ j)) cap
        (blockStageTrueKernel active ha (rebasedQuery query n) (rebasedQuery_measurable query hq n) O Θ j)
        (hiddenIndependentKernel dummy) k h := by
  rw [show resumedHiddenKernel (blockTargetKernel active ha query hq O Θ j) n k h=
      blockTargetKernel active ha query hq O Θ j (n+k) (historyResumeHidden n k h) from rfl,
    blockTargetKernel_apply,historyResumeHidden_initial,historyResumeHidden_public]
  rw [blockComparisonIndex_eq_stage active query Θ j _ (n+k) _ hs.1 hs.2.1 hs.2.2.1]
  simp only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_pos hs.2.2.2]
  rfl

end
end SecondOrder
