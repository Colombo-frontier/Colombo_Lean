import SecondOrder.BlockComparisonKernel

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem historyInitial_map {B C : Type u} (f : B → C) :
    ∀ n (h : FiniteHistory B A n), finiteHistoryInitial n (finiteHistoryMapInitial f n h)=f (finiteHistoryInitial n h) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro h; exact ih h.1

theorem historyMapInitial_comp {B C D : Type u} (f : B → C) (g : C → D) :
    ∀ n (h : FiniteHistory B A n), finiteHistoryMapInitial g n (finiteHistoryMapInitial f n h)=
      finiteHistoryMapInitial (g ∘ f) n h := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih => intro h; exact Prod.ext (ih h.1) rfl

/-- The comparison response with all hidden parameters fixed. -/
def blockFixedKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (n : ℕ) :
    Kernel (FiniteHistory S A n) A :=
  (indexedResponseKernel O).comap
    (fun h => ((Θ,query n h),blockComparisonIndex active query Θ n h))
    ((measurable_const.prodMk (hq n)).prodMk
      ((blockComparisonIndex_measurable active ha query hq n).comp measurable_prodMk_left))

instance blockFixedKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)] (Θ : Fin T → H) (n : ℕ) :
    IsMarkovKernel (blockFixedKernel active ha query hq O Θ n) := by
  unfold blockFixedKernel
  infer_instance

/-- Keep the other blocks fixed and draw the target block independently.
This is the same comparison kernel after a measurable substitution. -/
def blockTargetKernel (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    Kernel (FiniteHistory (H × S) A n) A :=
  (blockComparisonKernel active ha query hq O n).comap
    (finiteHistoryMapInitial (fun z : H × S => (Function.update Θ j z.1,z.2)) n)
    (finiteHistoryMapInitial_measurable
      (((measurable_update Θ).comp measurable_fst).prodMk measurable_snd) n)

instance blockTargetKernel_markov (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    IsMarkovKernel (blockTargetKernel active ha query hq O Θ j n) := by
  unfold blockTargetKernel
  infer_instance

theorem blockTargetKernel_apply (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) (Θ : Fin T → H) (j : Fin T) (n : ℕ)
    (h : FiniteHistory (H × S) A n) :
    blockTargetKernel active ha query hq O Θ j n h =
      O (blockComparisonIndex active query (Function.update Θ j (finiteHistoryInitial n h).1)
        n (finiteHistoryMapInitial Prod.snd n h))
        (Function.update Θ j (finiteHistoryInitial n h).1,query n (finiteHistoryMapInitial Prod.snd n h)) := by
  simp only [blockTargetKernel,Kernel.comap_apply,blockComparisonKernel_apply,blockHistoryIndex,
    blockHistoryInput,historyInitial_map,historyMapInitial_comp]
  rfl

def blockPreEntrySet (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (n : ℕ) :
    Set (FiniteHistory S A n) :=
  {h | blockComparisonProgress active query Θ n h<j.val ∧ blockComparisonIndex active query Θ n h<j.val}

theorem blockPreEntrySet_measurable (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) : MeasurableSet (blockPreEntrySet active query Θ j n) :=
  (measurableSet_lt ((blockComparisonProgress_measurable active ha query hq n).comp measurable_prodMk_left)
    measurable_const).inter
    (measurableSet_lt ((blockComparisonIndex_measurable active ha query hq n).comp measurable_prodMk_left)
      measurable_const)

/-- Before the first response whose index is the target block, the
comparison kernel cannot use that hidden block. This follows from the
extension's prefix dependence and the proved progress invariant. -/
theorem blockTargetKernel_preEntry_eq (active : Fin T → H → X → Prop)
    (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A)
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T) (n : ℕ) (h : FiniteHistory (H × S) A n)
    (hs : finiteHistoryMapInitial Prod.snd n h ∈ blockPreEntrySet active query Θ j n) :
    blockTargetKernel active ha query hq O Θ j n h =
      blockFixedKernel active ha query hq O Θ n (finiteHistoryMapInitial Prod.snd n h) := by
  let b := finiteHistoryMapInitial Prod.snd n h
  let θ := (finiteHistoryInitial n h).1
  have hlow : blockComparisonProgress active query Θ n b<j.val := hs.1
  have hindex : blockComparisonIndex active query Θ n b<j.val := hs.2
  have hprefix : ∀ i : Fin T, i.val<j.val → Θ i=Function.update Θ j θ i := by
    intro i hi
    have hij : i≠j := by intro he; subst i; omega
    rw [Function.update_of_ne hij]
  have hp : ∀ i : Fin T, i.val<blockComparisonProgress active query Θ n b+1 →
      Θ i=Function.update Θ j θ i := fun i hi => hprefix i (by omega)
  have he := blockComparisonIndex_prefix active query Θ (Function.update Θ j θ) n b hp
  rw [blockTargetKernel_apply]
  change O (blockComparisonIndex active query (Function.update Θ j θ) n b) (Function.update Θ j θ,query n b) =
    O (blockComparisonIndex active query Θ n b) (Θ,query n b)
  rw [←he]
  exact (hO (blockComparisonIndex active query Θ n b) Θ (Function.update Θ j θ) (query n b)
    (fun i hi => hprefix i (by omega))).symm

end
end SecondOrder
