import SecondOrder.BlockComparisonProgress

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

/-- Select a member of a countable kernel family at a measurable index. -/
def indexedResponseKernel {B : Type*} [MeasurableSpace B] (K : ℕ → Kernel B A) : Kernel (B × ℕ) A where
  toFun z := K z.2 z.1
  measurable' := measurable_from_prod_countable (fun n => (K n).measurable)

instance indexedResponseKernel_markov {B : Type*} [MeasurableSpace B]
    (K : ℕ → Kernel B A) [∀ n, IsMarkovKernel (K n)] : IsMarkovKernel (indexedResponseKernel K) where
  isProbabilityMeasure z := inferInstanceAs (IsProbabilityMeasure (K z.2 z.1))

def blockHistoryInput (query : ∀ n, FiniteHistory S A n → X) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) : (Fin T → H) × X :=
  ((finiteHistoryInitial n h).1,query n (finiteHistoryMapInitial Prod.snd n h))

theorem blockHistoryInput_measurable (query : ∀ n, FiniteHistory S A n → X)
    (hq : ∀ n, Measurable (query n)) (n : ℕ) : Measurable (blockHistoryInput (H := H) (T := T) query n) :=
  (measurable_fst.comp (finiteHistoryInitial_measurable n)).prodMk
    ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))

def blockHistoryProgress (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) : ℕ :=
  blockComparisonProgress active query (finiteHistoryInitial n h).1 n (finiteHistoryMapInitial Prod.snd n h)

def blockHistoryIndex (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) : ℕ :=
  blockComparisonIndex active query (finiteHistoryInitial n h).1 n (finiteHistoryMapInitial Prod.snd n h)

theorem blockHistoryProgress_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) :
    Measurable (blockHistoryProgress active query n) :=
  (blockComparisonProgress_measurable active ha query hq n).comp (historyHiddenPair_measurable n)

theorem blockHistoryIndex_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n)) (n : ℕ) :
    Measurable (blockHistoryIndex active query n) :=
  (blockComparisonIndex_measurable active ha query hq n).comp (historyHiddenPair_measurable n)

/-- The comparison response is sampled from the extension at the restricted
maximum active index. Replies are arbitrary Markov kernels. -/
def blockComparisonKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ) :
    Kernel (FiniteHistory ((Fin T → H) × S) A n) A :=
  (indexedResponseKernel O).comap
    (fun h => (blockHistoryInput query n h,blockHistoryIndex active query n h))
    ((blockHistoryInput_measurable query hq n).prodMk (blockHistoryIndex_measurable active ha query hq n))

instance blockComparisonKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (n : ℕ) :
    IsMarkovKernel (blockComparisonKernel active ha query hq O n) := by
  unfold blockComparisonKernel
  infer_instance

theorem blockComparisonKernel_apply (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ)
    (h : FiniteHistory ((Fin T → H) × S) A n) :
    blockComparisonKernel active ha query hq O n h =
      O (blockHistoryIndex active query n h) (blockHistoryInput query n h) := rfl

/-- The genuine interaction uses the unrestricted maximum active index. -/
def blockActualKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (n : ℕ) :
    Kernel (FiniteHistory ((Fin T → H) × S) A n) A :=
  (indexedResponseKernel O).comap
    (fun h => (blockHistoryInput query n h,
      blockActivationIndex active (finiteHistoryInitial n h).1
        (query n (finiteHistoryMapInitial Prod.snd n h)) T))
    ((blockHistoryInput_measurable query hq n).prodMk
      (blockActivationIndex_measurable active ha (fun h => (finiteHistoryInitial n h).1)
        (fun h => query n (finiteHistoryMapInitial Prod.snd n h)) (fun _ => T)
        (fun i => (measurable_pi_apply i).comp (measurable_fst.comp (finiteHistoryInitial_measurable n)))
        ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n)) measurable_const))

instance blockActualKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (n : ℕ) :
    IsMarkovKernel (blockActualKernel active ha query hq O n) := by
  unfold blockActualKernel
  infer_instance

end
end SecondOrder
