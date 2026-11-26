import SecondOrder.BlockTargetKernel
import SecondOrder.KernelStageExperiment

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

def blockStageIndex (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T)
    (n : ℕ) (h : FiniteHistory S A n) : ℕ := blockActivationIndex active Θ (query n h) j.val

theorem blockStageIndex_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : Measurable (blockStageIndex active query Θ j n) :=
  blockActivationIndex_measurable active ha (fun _ => Θ) (query n) (fun _ => j.val)
    (fun _ => measurable_const) (hq n) measurable_const

def blockStageSelected (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T)
    (n : ℕ) (h : FiniteHistory S A n) : Prop := blockStageIndex active query Θ j n h=j.val

theorem blockStageSelected_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : MeasurableSet {h | blockStageSelected active query Θ j n h} :=
  (blockStageIndex_measurable active ha query hq Θ j n) (measurableSet_singleton j.val)

/-- During the target stage, response indices inspect only earlier blocks.
The selected extension can still depend on the fresh target parameter. -/
def blockStageTrueKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    Kernel (FiniteHistory (H × S) A n) A :=
  (indexedResponseKernel O).comap
    (fun h => ((Function.update Θ j (finiteHistoryInitial n h).1,
      query n (finiteHistoryMapInitial Prod.snd n h)),
      blockStageIndex active query Θ j n (finiteHistoryMapInitial Prod.snd n h)))
    ((((measurable_update Θ).comp (measurable_fst.comp (finiteHistoryInitial_measurable n))).prodMk
      ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))).prodMk
      ((blockStageIndex_measurable active ha query hq Θ j n).comp
        (finiteHistoryMapInitial_measurable measurable_snd n)))

instance blockStageTrueKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    IsMarkovKernel (blockStageTrueKernel active ha query hq O Θ j n) := by
  unfold blockStageTrueKernel
  infer_instance

/-- Only the selected index is replaced by the supplied past-only
reference extension; all lower indices keep their original responses. -/
def blockStageReferenceKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (R : Kernel ((Fin T → H) × X) A)
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : Kernel (FiniteHistory S A n) A :=
  (indexedResponseKernel (fun p => if p=j.val then R else O p)).comap
    (fun h => ((Θ,query n h),blockStageIndex active query Θ j n h))
    ((measurable_const.prodMk (hq n)).prodMk (blockStageIndex_measurable active ha query hq Θ j n))

instance blockStageReferenceKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    IsMarkovKernel (blockStageReferenceKernel active ha query hq O R Θ j n) := by
  haveI : ∀ p, IsMarkovKernel (if p=j.val then R else O p) := by
    intro p
    split_ifs <;> infer_instance
  unfold blockStageReferenceKernel
  infer_instance

theorem blockStageKernels_same_unselected (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (R : Kernel ((Fin T → H) × X) A)
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) (h : FiniteHistory (H × S) A n)
    (hs : ¬ blockStageSelected active query Θ j n (finiteHistoryMapInitial Prod.snd n h)) :
    blockStageTrueKernel active ha query hq O Θ j n h =
      blockStageReferenceKernel active ha query hq O R Θ j n (finiteHistoryMapInitial Prod.snd n h) := by
  let b := finiteHistoryMapInitial Prod.snd n h
  let p := blockStageIndex active query Θ j n b
  have hp : p<j.val := by
    have hh := (blockActivationIndex_le active Θ (query n b) j.val).2
    have hn : p≠j.val := hs
    change p≤j.val at hh
    omega
  change O p (Function.update Θ j (finiteHistoryInitial n h).1,query n b) =
    (if p=j.val then R else O p) (Θ,query n b)
  rw [if_neg (by omega : p≠j.val)]
  apply hO
  intro i hi
  exact Function.update_of_ne (by intro he; subst i; omega) _ _

theorem blockStageKernels_kl (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (R : Kernel ((Fin T → H) × X) A)
    [∀ p, IsMarkovKernel (O p)] [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (n : ℕ) (h : FiniteHistory (H × S) A n) :
    klDiv (blockStageTrueKernel active ha query hq O Θ j n h)
      (blockStageReferenceKernel active ha query hq O R Θ j n (finiteHistoryMapInitial Prod.snd n h))≤ENNReal.ofReal κ := by
  by_cases hs : blockStageSelected active query Θ j n (finiteHistoryMapInitial Prod.snd n h)
  · let b := finiteHistoryMapInitial Prod.snd n h
    let Θ' := Function.update Θ j (finiteHistoryInitial n h).1
    have hp : blockStageIndex active query Θ j n b=j.val := hs
    change klDiv (O (blockStageIndex active query Θ j n b) (Θ',query n b))
      ((if blockStageIndex active query Θ j n b=j.val then R else O (blockStageIndex active query Θ j n b))
        (Θ,query n b))≤_
    rw [hp,if_pos rfl]
    have hr : R (Θ',query n b)=R (Θ,query n b) := hR Θ' Θ _ (fun i hi =>
      Function.update_of_ne (by intro he; subst i; omega) _ _)
    rw [←hr]
    exact hKL Θ' _
  · rw [blockStageKernels_same_unselected active ha query hq O R hO Θ j n h hs,klDiv_self]
    exact zero_le _

end
end SecondOrder
